-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.peel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:39.451936+00:00
-- url     : https://prove2.me/submissions/325651c3-ffa1-4158-a23e-2959d426cb76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_mem_lineV
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_sub_smul_mem_span_init
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_exists_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution {n : ℕ} (w : Fin (n + 1) → V) (hw : LinearIndependent E w) (M : Submodule (𝓞 E) V)
    (hM : M.FG) (hMX : M ≤ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E))
    {d : 𝓞 E} (hd : d ≠ 0) (hdw : d • w (Fin.last n) ∈ M) :
    ∃ (b : 𝓕) (u : V), b ≠ 0 ∧
      M = M ⊓ (Submodule.span E (Set.range (Fin.init w))).restrictScalars (𝓞 E) ⊔ lineV b u := by
  classical
  obtain ⟨f, hf1, hf0⟩ := exists_coord w hw
  let g : V →ₗ[𝓞 E] E := f.restrictScalars (𝓞 E)
  let b : 𝓕 := ⟨M.map g, FractionalIdeal.isFractional_of_fg (hM.map g)⟩
  have hmemb : ∀ x : E, x ∈ b ↔ ∃ m ∈ M, f m = x := fun x => Submodule.mem_map
  have hsmul : ∀ (r : 𝓞 E) (v : V), f (r • v) = algebraMap (𝓞 E) E r * f v := fun r v => by
    rw [← algebraMap_smul E r v, map_smul, smul_eq_mul]
  have hdb : algebraMap (𝓞 E) E d ∈ b := (hmemb _).2 ⟨_, hdw, by rw [hsmul, hf1, mul_one]⟩
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hdb
    exact hd (IsFractionRing.injective (𝓞 E) E (by rw [hdb, map_zero]))
  have key : ∀ z ∈ b * b⁻¹, ∃ u ∈ Submodule.span E (Set.range w),
      (∀ x ∈ b, x • u ∈ M) ∧ f u = z := by
    intro z hz
    refine FractionalIdeal.mul_induction_on hz ?_ ?_
    · intro i hi j hj
      obtain ⟨m, hmM, rfl⟩ := (hmemb i).1 hi
      refine ⟨j • m, Submodule.smul_mem _ _ (hMX hmM), fun x hx => ?_, ?_⟩
      · have hxj : x * j ∈ (1 : 𝓕) := by
          rw [← mul_inv_cancel₀ hb0]
          exact FractionalIdeal.mul_mem_mul hx hj
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hxj
        rw [smul_smul, ← hr, algebraMap_smul]
        exact M.smul_mem r hmM
      · rw [map_smul, smul_eq_mul, mul_comm]
    · rintro _ _ ⟨u1, hu1, h1, rfl⟩ ⟨u2, hu2, h2, rfl⟩
      refine ⟨u1 + u2, add_mem hu1 hu2, fun x hx => ?_, map_add f u1 u2⟩
      rw [smul_add]
      exact add_mem (h1 x hx) (h2 x hx)
  obtain ⟨u, huW, huM, hfu⟩ := key 1 (by
    rw [mul_inv_cancel₀ hb0]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
  refine ⟨b, u, hb0, le_antisymm ?_ ?_⟩
  · intro m hm
    have hfm : f m ∈ b := (hmemb _).2 ⟨m, hm, rfl⟩
    have hyW : m - f m • u ∈ Submodule.span E (Set.range w) :=
      sub_mem (hMX hm) (Submodule.smul_mem _ _ huW)
    have hfy : f (m - f m • u) = 0 := by
      rw [map_sub, map_smul, hfu, smul_eq_mul, mul_one, sub_self]
    have hy := sub_smul_mem_span_init w f hf1 hf0 hyW
    rw [hfy, zero_smul, sub_zero] at hy
    rw [show m = (m - f m • u) + f m • u by abel]
    exact Submodule.add_mem_sup ⟨sub_mem hm (huM _ hfm), hy⟩ (mem_lineV b u hfm)
  · refine sup_le inf_le_left (Submodule.span_le.2 ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact huM x hx
end Formalism.L2.SG.Pf.LatEx
