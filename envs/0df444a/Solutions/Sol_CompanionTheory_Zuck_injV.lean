-- Prove2me | solution 1 for CompanionTheory.Zuck.injV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:27:34.578981+00:00
-- url     : https://prove2.me/submissions/67c45491-19c8-4239-b1db-a23230f06521

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
namespace CompanionTheory.Zuck
theorem _root_.solution (S : Steps) (Lb : Lib t) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) < h) :
    ∃ T : {s // IsHCParam (shift b μ s)} → URep k r, (∀ s, (T s).R.IsDS ε (shift b μ s)) ∧
      JInj (N := M) IsHom (vr k r b, U) (fun s => one (T s)) ∧
      ∀ s, ∃ p, IsHom (vr k r b, U) (one (T s)) p ∧ p ≠ 0 := by
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  obtain ⟨T, hT, hin, hof⟩ := S.zuckH t Lb.zg k r ε μ U b h hU hg (by linarith)
  have hd := Lb.dec k r ε μ U h _ hU hg ht
  exact ⟨T, hT, S.inj k r _ _ T _ (S.okVr k r b) ⟨_, _, hU⟩ (fun s => ⟨_, _, hT s⟩) hd (by show 1 + _ + 1 ≤ _; omega) hin,
    fun s => S.occ k r _ _ _ (S.okVr k r b) ⟨_, _, hU⟩ ⟨_, _, hT s⟩ hd (by show 1 + _ + 1 ≤ _; omega) (hof s)⟩
end CompanionTheory.Zuck
