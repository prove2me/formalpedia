-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.gen_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:10:40.869237+00:00
-- url     : https://prove2.me/submissions/c065133d-d718-4e81-a3e5-9e84ca907d88

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) {p : ℕ} (w : Fin p → Λ)
    (hw : Submodule.span (𝓞 E) (Set.range w) = ⊤) (y : n → 𝒜) (hy : y ∈ latA (F := F) Λ) :
    ∃ s : Fin p → 𝒮, y = ∑ l, s l • (fun i => inclE (F := F) 𝔸 ((w l : n → E) i)) := by
  unfold latA latS at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨lam, hlam, rfl⟩ := hz
    have hmem : (⟨lam, hlam⟩ : Λ) ∈ Submodule.span (𝓞 E) (Set.range w) := by
      rw [hw]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hmem
    have hs : ∀ l, inclE (F := F) 𝔸 (algebraMap (𝓞 E) E (c l)) ∈ 𝒮 := by
      intro l
      unfold tensInt
      apply Subring.subset_closure
      left
      exact ⟨⟨algebraMap (𝓞 E) E (c l), RingHom.mem_range.2 ⟨c l, rfl⟩⟩, rfl⟩
    refine ⟨fun l => ⟨_, hs l⟩, ?_⟩
    have hl : lam = ∑ l, c l • (w l : n → E) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    funext i
    show inclE (F := F) 𝔸 (lam i) = _
    rw [hl]
    simp [Finset.sum_apply, Subring.smul_def, Algebra.smul_def, map_sum, map_mul]
    exact Finset.sum_congr rfl fun l _ => rfl
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul r a _ ha =>
    obtain ⟨s, rfl⟩ := ha
    exact ⟨fun l => r * s l, by simp [Finset.smul_sum, mul_smul]⟩
end Formalism.L2.Geo.Def.PC
