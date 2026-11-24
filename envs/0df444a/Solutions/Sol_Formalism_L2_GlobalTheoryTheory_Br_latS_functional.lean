-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Br.latS_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:14.95175+00:00
-- url     : https://prove2.me/submissions/a4014c50-05db-46f8-83f3-6ad0b8dc721a

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_finiteAdeleRing_nontrivial
import Theorems.Thm_Formalism_UG_P_inclE_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Br
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (f : Module.Dual E (Fin n → E))
    (hf : ∀ y ∈ Λ, f y = 0) (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : f x = 0 := by
  set c : Fin n → E := fun i => f (Pi.single i 1)
  have hfc : ∀ y : Fin n → E, f y = ∑ i, c i * y i := by
    intro y
    have hy : y = ∑ i, y i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have key : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∑ i, ι (c i) * u i = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      simp only [← map_mul, ← map_sum]
      rw [← hfc, hf y hy, map_zero]
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hu, hw, add_zero]
    | smul a u _ hu =>
      have h : ∑ i, ι (c i) * (a • u) i = (a : 𝒜) * ∑ i, ι (c i) * u i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply]
        show _ * ((a : 𝒜) * u i) = _
        ring
      rw [h, hu, mul_zero]
  have h1 := key _ hx
  simp only [← map_mul, ← map_sum] at h1
  rw [← hfc] at h1
  exact inclE_injective_fin h1
where
  inclE_injective_fin {a : E} (h : ι a = 0) : a = 0 :=
    have := finiteAdeleRing_nontrivial (F := F)
    Formalism.UG.P.inclE_injective F E (FiniteAdeleRing (𝓞 F) F) (by rw [h, map_zero])
end Formalism.L2.GlobalTheoryTheory.Br
