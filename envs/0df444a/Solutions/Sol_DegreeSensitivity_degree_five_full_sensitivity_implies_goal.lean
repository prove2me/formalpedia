-- Prove2me | solution 1 for DegreeSensitivity.degree_five_full_sensitivity_implies_goal
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T16:47:31.040038+00:00
-- url     : https://prove2.me/submissions/dd566bff-b3e3-47f3-bba1-a7008f58e68f

import Definitions.Def_polyDegree
import Definitions.Def_sensitivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

open MvPolynomial
namespace DegreeSensitivity

lemma exponent_bound : Real.log 6 / Real.log 3 < (18 : ℝ) / 11 := by
  have h := Real.log_lt_log (x := (6 : ℝ)^11) (y := (3 : ℝ)^18) (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hp).2
  nlinarith

lemma power_bound : (5 : ℝ) ^ (Real.log 6 / Real.log 3) < 14 := by
  have h : (5 : ℝ) ^ ((18 : ℝ)/11) < 14 := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num) (show (0 : ℝ) < 11 by norm_num)).1
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) exponent_bound).trans h

lemma affine_eval_add {σ : Type*} (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ 1)
    (u v : σ → ℝ) :
    eval (u + v) p + eval (0 : σ → ℝ) p = eval u p + eval v p := by
  classical
  have hm (s : σ →₀ ℕ) (hs : s ∈ p.support) :
      eval (u + v) (monomial s (coeff s p)) + eval (0 : σ → ℝ) (monomial s (coeff s p)) =
      eval u (monomial s (coeff s p)) + eval v (monomial s (coeff s p)) := by
    have hd := (le_totalDegree hs).trans hp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hz | ho
    · have he : s = 0 := by
        ext i
        have hi : s i ≤ s.sum (fun _ e => e) := by
          by_cases hh : i ∈ s.support
          · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hh
          · simp_all
        simpa [hz] using hi
      subst s
      simp
    · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff s).mp ho
      simp only [eval_monomial]
      simp [Finsupp.prod_single_index, mul_add]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hm

lemma degree_gt_one {g : BoolFunc 14} (hz : g (fun _ => false) = false)
    (hu : ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true) :
    1 < polyDegree g := by
  classical
  by_contra hn
  have hd : polyDegree g ≤ 1 := by omega
  obtain ⟨p, hp, he⟩ := Nat.find_spec (show ∃ d, HasPolyRep g d from ⟨14, hasPolyRep_card g⟩)
  have hp1 : p.totalDegree ≤ 1 := hp.trans hd
  let x : Fin 14 → Bool := Function.update (fun _ => false) 0 true
  let y : Fin 14 → Bool := Function.update (fun _ => false) 1 true
  let z : Fin 14 → Bool := Function.update x 1 true
  let u : Fin 14 → ℝ := fun i => if x i then 1 else 0
  let v : Fin 14 → ℝ := fun i => if y i then 1 else 0
  have huv : u + v = fun i => if z i then (1 : ℝ) else 0 := by
    funext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp_all [u, v, x, y, z, Function.update_apply]
  have ha := affine_eval_add p hp1 u v
  rw [huv, he z] at ha
  have hzero : eval (0 : Fin 14 → ℝ) p = 0 := by simpa [hz] using he (fun _ => false)
  have hx : eval u p = 1 := by simpa [u, x, hu] using he x
  have hy : eval v p = 1 := by simpa [v, y, hu] using he y
  rw [hzero, hx, hy] at ha
  split_ifs at ha <;> norm_num at ha

 theorem degree_five_full_sensitivity_implies_goal
    (h : ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
      ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true) :
    ∃ (n : ℕ) (f : BoolFunc n), 1 < n ∧ 1 < polyDegree f ∧
      (polyDegree f : ℝ) ^ (Real.log 6 / Real.log 3) <
        (sensitivityAt f (fun _ => false) : ℝ) := by
  obtain ⟨g, hd, hz, hu⟩ := h
  refine ⟨14, g, by norm_num, degree_gt_one hz hu, ?_⟩
  have hs : sensitivityAt g (fun _ => false) = 14 := by
    simp [sensitivityAt, flipBit, hz, hu]
  rw [hs]
  exact (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hd)
    (by positivity : 0 ≤ Real.log 6 / Real.log 3)).trans_lt power_bound

#print axioms degree_five_full_sensitivity_implies_goal
end DegreeSensitivity


theorem solution : (
  (∃ (g : BoolFunc (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))),
      And
        (@LE.le Nat instLENat (@polyDegree (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) g)
          (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        (And
          (@Eq Bool (g fun (x : Fin (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))) => Bool.false)
            Bool.false)
          (∀ (i : Fin (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))),
            @Eq Bool
              (g
                (@Function.update (Fin (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                  (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))) => Bool)
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                  (fun (x : Fin (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))) => Bool.false) i Bool.true))
              Bool.true))) →
    ∃ (n : Nat) (f : BoolFunc n),
      And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
        (And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@polyDegree n f))
          (@LT.lt Real Real.instLT
            (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
              (@Nat.cast Real Real.instNatCast (@polyDegree n f))
              (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                (Real.log
                  (@OfNat.ofNat Real (nat_lit 6)
                    (@instOfNatAtLeastTwo Real (nat_lit 6) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
                (Real.log
                  (@OfNat.ofNat Real (nat_lit 3)
                    (@instOfNatAtLeastTwo Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
            (@Nat.cast Real Real.instNatCast (@sensitivityAt n f fun (x : Fin n) => Bool.false))))
) := @DegreeSensitivity.degree_five_full_sensitivity_implies_goal
