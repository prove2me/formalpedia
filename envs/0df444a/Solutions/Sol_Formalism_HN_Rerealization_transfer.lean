-- Prove2me | solution 1 for Formalism.HN.Rerealization.transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:10.259339+00:00
-- url     : https://prove2.me/submissions/b161b482-cc3e-4c4d-9b66-466a67023a14

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Theorems.Thm_Formalism_HN_Rerealization_covol_rk_eq
import Theorems.Thm_Formalism_HN_Rerealization_covol_eq_exp
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_shiftInv_isSat_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.Rerealization
variable {R V E E₂ : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
namespace Formalism.HN.Rerealization
theorem _root_.solution (ρ : V →+ E) (ρ₂ : V →+ E₂) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (L : Submodule R V)
    (hL : IsLat ρ L) (hL₂ : IsLat ρ₂ L) :
    (∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧
      rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N) ∧
    (∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N) ∧
    (∀ N : Submodule R V, IsSat ρ L N →
      Formalism.F.covol (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.covol (Formalism.F.quot (zl ρ L) (zl ρ N)) ∧
      Formalism.F.slope (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) =
        Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N))) := by
  obtain ⟨a1, -, -, -, -, -, -, a8⟩ := saturation_basic_properties R V E ρ L hL
  obtain ⟨b1, -, -, -, -, -, -, b8⟩ := saturation_basic_properties R V E₂ ρ₂ L hL₂
  have T1 : ∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧
      rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N := by
    intro N hN
    obtain ⟨c1, c2⟩ := covol_rk_eq ρ ρ₂ hn N.toAddSubgroup (a1 N hN).2 (b1 N hN).2
    have h1 : Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) := c1
    have h2 : rk ρ₂ N = rk ρ N := c2
    have h3 : deg ρ₂ N = deg ρ N := by
      unfold deg Formalism.F.deg
      rw [h1]
    refine ⟨h1, h2, h3, ?_⟩
    unfold slope Formalism.F.slope
    exact congrArg₂ (· / ·) h3 (congrArg (fun n : ℕ => (n : ℝ)) h2)
  have T2 : ∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N := by
    intro N
    rw [shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]
    constructor
    · rintro ⟨hNL, h⟩
      refine ⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩
      rw [(T1 N' h2).2.1, (T1 N hNL).2.1, h3]
    · rintro ⟨hNL, h⟩
      refine ⟨hNL, fun N' h1 h2 h3 => h N' h1 h2 ?_⟩
      rw [← (T1 N' h2).2.1, ← (T1 N hNL).2.1, h3]
  refine ⟨T1, T2, ?_⟩
  intro N hS
  have hS₂ := (T2 N).2 hS
  obtain ⟨q1, -, q3⟩ := a8 N hS
  obtain ⟨r1, -, r3⟩ := b8 N hS₂
  have hrk : Formalism.F.rk (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ N)) := by
    rw [q1, r1, (T1 L le_rfl).2.1, (T1 N hS.1).2.1]
  have hdeg : Formalism.F.deg (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) =
      Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ N)) := by
    rw [q3, r3, (T1 L le_rfl).2.2.1, (T1 N hS.1).2.2.1]
  refine ⟨?_, ?_⟩
  · rw [covol_eq_exp _ (Formalism.F.degQuot E₂ _ _ hL₂.2 hS₂.2).1,
      covol_eq_exp _ (Formalism.F.degQuot E _ _ hL.2 hS.2).1, hdeg]
  · unfold Formalism.F.slope
    rw [hdeg, hrk]
end Formalism.HN.Rerealization
