-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.back_subG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:36:23.029745+00:00
-- url     : https://prove2.me/submissions/d7026365-ce51-4408-b168-be140c3be527

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_gram_matrix_mul_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_sum_coS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_subG_X
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
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
variable {r tau}
variable (r tau)
variable {r tau gm}
variable (r tau gm)
variable {r tau gm}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) * MvPolynomial.X x) (subG r tau gm plc Q) = Q := by
  have h : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) *
      (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))).comp (subG r tau gm plc) =
      AlgHom.id C _ := by
    apply MvPolynomial.algHom_ext
    intro y
    rw [AlgHom.comp_apply, subG_X, map_sum, AlgHom.id_apply]
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    have hs : ∀ col, (∑ x, MvPolynomial.C (coS r tau gm plc (lam r tau plc ((eW r tau N y).1, col)) x) *
        (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C)) =
        ∑ g, MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :=
      fun col => sum_coS plc inj (eW r tau N y).1 col (fun c x => MvPolynomial.C c * MvPolynomial.X x) (by simp)
    simp only [hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ g, (∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
        (MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) *
          (MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :
            MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))) =
        MvPolynomial.C (if g = (eW r tau N y).2 then 1 else 0) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) := by
      intro g
      rw [← gram_matrix_mul_right gm_hyp (eW r tau N y).1 (eW r tau N y).2 g, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun col _ => ?_
      rw [map_mul]; ring
    simp only [h2]
    rw [Finset.sum_eq_single (eW r tau N y).2]
    · simp
    · intro g _ hg; simp [hg]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact congrArg (fun φ => φ Q) h
end Formalism.L2.FormalSeriesBounds.RF
