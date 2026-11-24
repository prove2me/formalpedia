-- Prove2me | solution 1 for BB6Kit.prop37
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T06:34:51.268803+00:00
-- url     : https://prove2.me/submissions/b7fbef6c-f6d9-4751-9361-a85611df85b3

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi
import Theorems.Thm_BB6Kit_prop37_expand
import Theorems.Thm_BB6Kit_prop37_term

open Finset

namespace P37

lemma key {N : ℕ} (D P Lp E : ℝ) (ψ : Finset (Fin N) → ℂ) (hP : 0 < P) (hLp : 0 ≤ Lp)
    (hexp : (D : ℂ) = (P : ℂ) * ∑ I ∈ (univ : Finset (Fin N)).powerset, ((Lp ^ (N - I.card) : ℝ) : ℂ) * ψ I)
    (hterm : ∀ I : Finset (Fin N), Lp ^ (N - I.card) * ‖ψ I‖ < Real.exp E) :
    |D| < P * 2 ^ N * Real.exp E := by
  have h1 : |D| = ‖(D : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h1, hexp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hP.le]
  have h2 : ‖∑ I ∈ (univ : Finset (Fin N)).powerset, ((Lp ^ (N - I.card) : ℝ) : ℂ) * ψ I‖ ≤
      ∑ I ∈ (univ : Finset (Fin N)).powerset, Lp ^ (N - I.card) * ‖ψ I‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro I _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hLp _)]
  have h3 : ∑ I ∈ (univ : Finset (Fin N)).powerset, Lp ^ (N - I.card) * ‖ψ I‖ <
      ∑ I ∈ (univ : Finset (Fin N)).powerset, Real.exp E :=
    sum_lt_sum_of_nonempty ⟨∅, empty_mem_powerset _⟩ (fun I _ => hterm I)
  rw [sum_const, card_powerset, card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  push_cast at h3
  calc P * ‖∑ I ∈ (univ : Finset (Fin N)).powerset, ((Lp ^ (N - I.card) : ℝ) : ℂ) * ψ I‖
      ≤ P * ∑ I ∈ (univ : Finset (Fin N)).powerset, Lp ^ (N - I.card) * ‖ψ I‖ :=
        mul_le_mul_of_nonneg_left h2 hP.le
    _ < P * (2 ^ N * Real.exp E) := mul_lt_mul_of_pos_left h3 hP
    _ = P * 2 ^ N * Real.exp E := by ring

end P37

theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0) (hρ : 2 ≤ ρ)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hsmall : BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) < ρ ^ (-((K : ℝ) * L))) :
    |BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst| <
      Real.exp (BB6Kit.MK L N rst Prod.fst * Real.log (α1 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.1) * Real.log (α2 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.2) * Real.log (α3 : ℝ) + ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) + Real.log (N.factorial : ℝ) + (N : ℝ) * Real.log 2 +
        (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log (BB6Kit.bK K R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3)) -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
          16 / (3 * (K : ℝ) ^ 2 * L)) * Real.log ρ + 0.001) := by
  have hexp := BB6Kit.prop37_expand K L R S T N b1 b2 b3 α1 α2 α3 hK hL hN hRST hα1 hα2 hα3 hb1 hb2 hb3 hΛ
    kml rst hrows hcols
  have hterm := BB6Kit.prop37_term K L R S T N b1 b2 b3 α1 α2 α3 ρ hK hL hN hRST hα1 hα2 hα3 hind hb1 hb2 hb3
    hgcd hΛ hρ kml rst hrows hcols hsmall
  have ha1 : (0:ℝ) < α1 := by exact_mod_cast (show 0 < α1 by omega)
  have ha2 : (0:ℝ) < α2 := by exact_mod_cast (show 0 < α2 by omega)
  have ha3 : (0:ℝ) < α3 := by exact_mod_cast (show 0 < α3 by omega)
  have hP : (0:ℝ) < (α1 : ℝ) ^ (BB6Kit.MK L N rst Prod.fst) * (α2 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.1)) *
      (α3 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.2)) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos ha1 _) (Real.rpow_pos_of_pos ha2 _)) (Real.rpow_pos_of_pos ha3 _)
  have hLp : 0 ≤ BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) := by
    unfold BB6Kit.lamPrime; positivity
  have hk := P37.key _ _ _ _ _ hP hLp hexp hterm
  refine lt_of_lt_of_eq hk ?_
  have h2N : (2:ℝ) ^ N = Real.exp ((N:ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [Real.rpow_def_of_pos ha1, Real.rpow_def_of_pos ha2, Real.rpow_def_of_pos ha3, h2N]
  simp only [← Real.exp_add]
  congr 1
  ring
