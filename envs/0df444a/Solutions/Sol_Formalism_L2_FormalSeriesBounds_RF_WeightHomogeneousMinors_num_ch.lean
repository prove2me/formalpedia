-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.num_ch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:55.559715+00:00
-- url     : https://prove2.me/submissions/340c9804-b5f6-45b9-b59c-1e284495b310

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
theorem _root_.solution (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) (u : ℕ) :
    u • (if X.n ≤ X.n ∧ X.n ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < X.n then 1 else 0) =
      ∑ k ∈ Finset.Icc (c0 + 1) (r (tau o0 g0 t0)), (if g0 = g ∧ t0 = t ∧ k = X.n then u else 0) := by
  by_cases hg : g0 = g ∧ t0 = t
  · obtain ⟨rfl, rfl⟩ := hg
    rw [rkF_eq X hty]
    simp only [le_refl, true_and, eq_self_iff_true]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_Icc]
    by_cases hc : X.n ≤ r (tau o0 g0 t0) ∧ c0 < X.n
    · rw [if_pos hc, if_pos ⟨by omega, hc.1⟩, smul_eq_mul, mul_one]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.2, by omega⟩), smul_zero]
  · rw [Finset.sum_eq_zero (fun k _ => if_neg (fun h => hg ⟨h.1, h.2.1⟩))]
    rw [if_neg (fun h => hg ⟨h.2.2.1.1.symm, h.2.2.1.2.symm⟩), smul_zero]
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
