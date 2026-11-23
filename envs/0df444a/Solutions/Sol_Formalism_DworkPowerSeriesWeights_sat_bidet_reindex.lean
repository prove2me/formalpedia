-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_bidet_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:39.317126+00:00
-- url     : https://prove2.me/submissions/18446170-2d82-4951-bfc4-e0e8153002ec

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_card_fiber
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_satMinor_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_bidet_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_sigma_cast
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_prod_fibers
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (R : Type) [CommRing R] {r n k C : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n)
    (p : Fin C → ℕ) (hp : ∀ c, p c ≤ n) (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p)
    (I : ∀ i, Fin (sz i) → Fin r) : ∃ A : ∀ c, Fin (p c) → Fin r, bideterminant R sz hsz I = bideterminant R p hp A := by
  classical
  have e : ∀ j, {c // p c = j + 1} ≃ {i // sz i = j + 1} := fun j =>
    Fintype.equivOfCardEq (sat_card_fiber sz p hsz hp h j)
  have hk : ∀ c, p c ≠ 0 → p c = p c - 1 + 1 := fun c hc => by omega
  let A : ∀ c, Fin (p c) → Fin r := fun c =>
    if h0 : p c = 0 then fun i => (Fin.cast h0 i).elim0
    else fun i => I (e (p c - 1) ⟨c, hk c h0⟩).1
      (Fin.cast ((hk c h0).trans (e (p c - 1) ⟨c, hk c h0⟩).2.symm) i)
  have hA : ∀ j (c : {c // p c = j + 1}),
      (⟨p c.1, A c.1⟩ : (j : ℕ) × (Fin j → Fin r)) = ⟨sz (e j c).1, I (e j c).1⟩ := by
    rintro j ⟨c, hc⟩
    have h0 : p c ≠ 0 := by omega
    have hj : p c - 1 = j := by omega
    subst hj
    simp only [A, dif_neg h0]
    exact sat_sigma_cast _ _
  refine ⟨A, ?_⟩
  rw [sat_bidet_eq, sat_bidet_eq,
    sat_prod_fibers sz hsz _ (fun i hi => satMinor_zero R r n _ hi),
    sat_prod_fibers p hp _ (fun c hc => satMinor_zero R r n _ hc)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Fintype.prod_equiv (e j) (fun c => satMinor R r n ⟨p c.1, A c.1⟩)
    (fun i => satMinor R r n ⟨sz i.1, I i.1⟩)]
  intro c
  rw [hA j c]
end Formalism.DworkPowerSeriesWeights
