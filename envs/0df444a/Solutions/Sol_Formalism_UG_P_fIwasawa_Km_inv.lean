-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_Km_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:00:20.967963+00:00
-- url     : https://prove2.me/submissions/4b212abf-ed48-43e0-b22d-8694ca7d353a

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
private theorem antiJ_mul_apply' (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (antiJ L n * N) i j = N (Fin.rev i) j := by
  have hi := i.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [antiJ_apply_adelic_iwasawa_hecke, if_pos (by rw [Fin.val_rev]; omega), one_mul]
  · intro k _ hk
    have hk' := k.isLt
    rw [antiJ_apply_adelic_iwasawa_hecke, if_neg, zero_mul]
    intro h
    apply hk
    ext
    rw [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem cT_apply_eq_sigma_transpose (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    cT σ N i j = σ (N j i) := rfl
private theorem cT_mul_reverse (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]
private theorem cT_one_eq_one : cT σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  rw [cT_apply_eq_sigma_transpose]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]
private theorem antiJ_mul_antiJ : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul_apply', antiJ_apply_adelic_iwasawa_hecke, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [Fin.val_rev, ← h]; omega)]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    ext
    rw [Fin.val_rev] at h'
    omega
end FIwasawaRed
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {A : Matrix (Fin n) (Fin n) L}
    (hA : fIwasawaKm σ A) : fIwasawaKm σ (fIwasawaInv σ A) := by
  unfold fIwasawaKm at hA ⊢
  obtain ⟨hAu, hAi⟩ := hA
  have hu := hAu
  unfold fIwasawaUn at hu
  have hBA : fIwasawaInv σ A * A = 1 := by
    unfold fIwasawaInv
    calc antiJ L n * cT σ A * antiJ L n * A = antiJ L n * (cT σ A * antiJ L n * A) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, antiJ_mul_antiJ]
  have hAB : A * fIwasawaInv σ A = 1 := mul_eq_one_comm.mp hBA
  refine ⟨?_, ?_⟩
  · unfold fIwasawaUn
    calc cT σ (fIwasawaInv σ A) * antiJ L n * fIwasawaInv σ A
        = cT σ (fIwasawaInv σ A) * (cT σ A * antiJ L n * A) * fIwasawaInv σ A := by rw [hu]
      _ = cT σ (A * fIwasawaInv σ A) * antiJ L n * (A * fIwasawaInv σ A) := by
          rw [cT_mul_reverse]
          simp only [Matrix.mul_assoc]
      _ = antiJ L n := by rw [hAB, cT_one_eq_one, Matrix.one_mul, Matrix.mul_one]
  · unfold fIwasawaInt at hAi ⊢
    intro i j
    unfold fIwasawaInv
    rw [mul_antiJ_apply', antiJ_mul_apply', cT_apply_eq_sigma_transpose, hσv]
    exact hAi _ _
end Formalism.UG.P
