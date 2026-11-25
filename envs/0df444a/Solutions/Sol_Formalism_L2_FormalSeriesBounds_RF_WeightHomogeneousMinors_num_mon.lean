-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.num_mon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:57.005692+00:00
-- url     : https://prove2.me/submissions/9d7a8430-13c3-4b00-8f71-abd0ca78cf09

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_rkF_eq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]
variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)
include hty
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (r (tau o0 g0 t0)),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by
  by_cases hg : g = g0
  · subst hg
    rw [Finset.sum_eq_single t0]
    · rw [rkF_eq X hty]
      have hL : ∀ k ∈ Finset.Icc 1 (min N (r (tau o0 g t0))),
          e t0 k • (if k ≤ N ∧ k ≤ r (tau o0 g t0) ∧ (g = g ∧ t0 = t0) ∧ c0 < k then 1 else 0) =
            if c0 < k then e t0 k else 0 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        by_cases hc : c0 < k
        · rw [if_pos ⟨by omega, by omega, ⟨rfl, rfl⟩, hc⟩, if_pos hc, smul_eq_mul, mul_one]
        · rw [if_neg (fun h => hc h.2.2.2), if_neg hc, smul_zero]
      rw [Finset.sum_congr rfl hL, ← Finset.sum_filter, ← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, eq_self_iff_true, true_and]
      omega
    · intro t _ ht
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (fun h => ht h.2.2.1.2), smul_zero]
    · simp
  · trans 0
    · exact Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun k _ => by
        rw [if_neg (fun h => hg h.2.2.1.1), smul_zero]
    · exact (Finset.sum_eq_zero fun k _ => if_neg (fun h => hg h.1.symm)).symm
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
