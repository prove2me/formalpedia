-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_gram_un
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:32.593115+00:00
-- url     : https://prove2.me/submissions/aceb65f9-0f8e-40dd-97f8-7c22a834bab9

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaRed
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
private theorem antiJ_apply_adelic_iwasawa_hecke (i j : Fin n) :
    antiJ L n i j = if (i : ℕ) + j + 1 = n then 1 else 0 := rfl
private theorem mul_antiJ_apply' (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (N * antiJ L n) i j = N i (Fin.rev j) := by
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · rw [antiJ_apply_adelic_iwasawa_hecke, if_pos (by rw [Fin.val_rev]; omega), mul_one]
  · intro k _ hk
    have hk' := k.isLt
    rw [antiJ_apply_adelic_iwasawa_hecke, if_neg, mul_zero]
    intro h
    apply hk
    ext
    rw [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem cT_apply_eq_sigma_transpose (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    cT σ N i j = σ (N j i) := rfl
end FIwasawaRed
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (a b : Fin n) :
    ∑ j, σ (M (Fin.rev j) a) * M j b = if b = Fin.rev a then 1 else 0 := by
  unfold fIwasawaUn at hM
  have h := congrFun (congrFun hM a) b
  rw [Matrix.mul_apply] at h
  simp only [mul_antiJ_apply', cT_apply_eq_sigma_transpose, antiJ_apply_adelic_iwasawa_hecke] at h
  rw [h]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : b = Fin.rev a
  · rw [if_pos, if_pos hab]
    rw [hab, Fin.val_rev]
    omega
  · rw [if_neg, if_neg hab]
    intro h'
    apply hab
    ext
    rw [Fin.val_rev]
    omega
end Formalism.UG.P
