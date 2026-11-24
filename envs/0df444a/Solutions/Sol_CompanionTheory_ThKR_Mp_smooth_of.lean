-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.smooth_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:51.295922+00:00
-- url     : https://prove2.me/submissions/2bde918b-ca3a-4f07-ae04-9f18e74c9d54

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOrb
import Theorems.Thm_CompanionTheory_ThKR_Mp_hasFDerivAt_orb
import Theorems.Thm_CompanionTheory_ThKR_Mp_contDiff_dm
import Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_om


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (hT : TopG l) (hN : NearOne l) (hD : SecDer l) : Smooth l := by
  intro k γ hγ hs f
  have hd : ∀ a b, Differentiable ℝ fun t => (pr (γ t) : Mat l) a b := fun a b =>
    (hs a b).differentiable (by simp)
  suffices H : ∀ n : ℕ, ∀ g : Sch l, ContDiff ℝ n (orb γ g) from contDiff_infty.2 fun n => H n f
  intro n
  induction n with
  | zero =>
    intro g
    have := (contDiff_zero (𝕜 := ℝ) (f := orb γ g)).2 ((continuous_om (schwartzToL2 l g)).comp hγ)
    exact_mod_cast this
  | succ n ih =>
    intro g
    have key := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (f := orb γ g) (n := n)).2
      ⟨fun t => ∑ a, ∑ b, (dm γ t a b).smulRight (orb γ (Qd (Matrix.single a b 1) g) t),
        ContDiff.sum fun a _ => ContDiff.sum fun b _ => (contDiff_dm γ hs a b n).smulRight (ih _),
        fun t => hasFDerivAt_orb hT hN hD γ hγ hd g t⟩
    exact_mod_cast key
end CompanionTheory.ThKR.Mp
