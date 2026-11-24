-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.beta_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:18.569272+00:00
-- url     : https://prove2.me/submissions/37a78b90-eea6-42ff-8331-5ddf55411372

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_pair_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bM_pair
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_aa_eq
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution [Fintype H] [DecidableEq H] {N1 : ℕ}
    (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0) (u : H → K) :
    MvPowerSeries.subst (fun z : (Bool × H) × Fin N0 × Fin N1 =>
        (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
          MvPowerSeries (Bool × H × Fin N0 × Fin N1) K))
      (∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
        MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)) =
      ∑ i : H × Fin N0 × Fin N1, MvPowerSeries.C (u i.1) * MvPowerSeries.X (false, i) *
        MvPowerSeries.X (true, i) := by
  have hs : MvPowerSeries.HasSubst (fun z : (Bool × H) × Fin N0 × Fin N1 =>
        (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
          MvPowerSeries (Bool × H × Fin N0 × Fin N1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by simp
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_sum]
  simp only [map_mul, MvPowerSeries.substAlgHom_X]
  simp only [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_comm (f := fun (k : Fin N0) (b : Fin N1) => MvPowerSeries.C (u t) *
      MvPowerSeries.X (false, t, k, b) * MvPowerSeries.X (true, t, k, b))]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [aa_eq]
  have h := pair_sum (R' := MvPowerSeries (Bool × H × Fin N0 × Fin N1) K)
    (MvPowerSeries.C (σ := Bool × H × Fin N0 × Fin N1) (R := K)) (bM x (false, t)) (bM x (true, t))
    (bM_pair x hx t)
    (fun i => (MvPowerSeries.X (false, t, i, b) : MvPowerSeries (Bool × H × Fin N0 × Fin N1) K))
    (fun i => (MvPowerSeries.X (true, t, i, b) : MvPowerSeries (Bool × H × Fin N0 × Fin N1) K))
  exact h
end Formalism.DworkPowerSeriesWeights
