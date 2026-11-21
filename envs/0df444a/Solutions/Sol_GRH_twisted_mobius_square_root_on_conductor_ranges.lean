-- Prove2me | solution 1 for GRH.twisted_mobius_square_root_on_conductor_ranges
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:55:01.936341+00:00
-- url     : https://prove2.me/submissions/8ef09325-82e8-4458-a677-28dd9865b215

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

section
open Finset

namespace MasulloConductor

/-- Sum of squared block sums over all nodes in a complete dyadic block tree. -/
noncomputable def dyadicTreeEnergy (a : ℕ → ℂ) : ℕ → ℕ → ℝ
  | 0, u => ‖a u‖^2
  | J+1, u => ‖∑ k ∈ range (2^(J+1)), a (u+k)‖^2 +
      dyadicTreeEnergy a J u + dyadicTreeEnergy a J (u+2^J)

theorem dyadicTreeEnergy_nonneg (a : ℕ → ℂ) (J u : ℕ) : 0 ≤ dyadicTreeEnergy a J u := by
  induction J generalizing u with
  | zero => exact sq_nonneg _
  | succ J ih => exact add_nonneg (add_nonneg (sq_nonneg _) (ih _)) (ih _)

theorem full_block_sq_le_dyadicTreeEnergy (a : ℕ → ℂ) (J u : ℕ) :
    ‖∑ k ∈ range (2^J), a (u+k)‖^2 ≤ dyadicTreeEnergy a J u := by
  cases J with
  | zero => simp [dyadicTreeEnergy]
  | succ J => dsimp [dyadicTreeEnergy]; linarith [dyadicTreeEnergy_nonneg a J u,
      dyadicTreeEnergy_nonneg a J (u+2^J)]

private lemma weighted_two_terms {d x y E : ℝ} (hd : 0 < d) (hy : y^2 ≤ d*E) :
    (x+y)^2 ≤ (d+1)*(x^2+E) := by
  have hprod : 0 ≤ (d*x^2+E-2*x*y)*d := by nlinarith only [sq_nonneg (d*x-y),hy]
  have hcross := nonneg_of_mul_nonneg_left hprod hd
  nlinarith only [hy,hcross]

/-- The deterministic dyadic maximal estimate for all finite prefixes, including both endpoints. -/
theorem prefix_sq_le_dyadicTreeEnergy (a : ℕ → ℂ) (J u N : ℕ) (hN : N ≤ 2^J) :
    ‖∑ k ∈ range N, a (u+k)‖^2 ≤ ((J:ℝ)+1) * dyadicTreeEnergy a J u := by
  induction J generalizing u N with
  | zero =>
    have hN' : N ≤ 1 := by simpa using hN
    have hh : N = 0 ∨ N = 1 := by omega
    rcases hh with rfl|rfl <;> simp [dyadicTreeEnergy]
  | succ J ih =>
    let H := 2^J
    have hbig : N ≤ H+H := by simpa only [H, pow_succ, Nat.mul_two] using hN
    have hL0 := dyadicTreeEnergy_nonneg a J u
    have hR0 := dyadicTreeEnergy_nonneg a J (u+H)
    have htop := sq_nonneg ‖∑ k ∈ range (2^(J+1)), a (u+k)‖
    have hfac : (0:ℝ) < (J:ℝ)+1 := by positivity
    by_cases hleft : N ≤ H
    · have hleft' := ih u N hleft
      have hEL : dyadicTreeEnergy a J u ≤ dyadicTreeEnergy a (J+1) u := by
        dsimp only [dyadicTreeEnergy]; linarith
      refine hleft'.trans (mul_le_mul ?_ hEL hL0 (by positivity))
      push_cast; linarith
    · have hright : N-H ≤ 2^J := by change N-H ≤ H; omega
      have split : (∑ k ∈ range N, a (u+k)) =
          (∑ k ∈ range H, a (u+k)) + ∑ k ∈ range (N-H), a ((u+H)+k) := by
        have hn : N = H + (N-H) := by omega
        conv_lhs => rw [hn,sum_range_add]
        simp only [Nat.add_assoc]
      rw [split]
      set X := ∑ k ∈ range H, a (u+k)
      set Y := ∑ k ∈ range (N-H), a ((u+H)+k)
      have hY : ‖Y‖^2 ≤ ((J:ℝ)+1)*dyadicTreeEnergy a J (u+H) := ih (u+H) (N-H) hright
      have hX : ‖X‖^2 ≤ dyadicTreeEnergy a J u := full_block_sq_le_dyadicTreeEnergy a J u
      have hXY : ‖X+Y‖^2 ≤ (‖X‖+‖Y‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le X Y) 2
      refine hXY.trans ((weighted_two_terms (x := ‖X‖) hfac hY).trans ?_)
      push_cast
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp only [dyadicTreeEnergy]
      linarith

end MasulloConductor
end

section
open Finset
namespace MasulloConductor

private theorem reciprocal_square_sum (n : ℕ) :
    (∑ j ∈ range n, 1/((j:ℝ)+1)^2) ≤ 2 := by
  let H (j : ℕ) := 2/((j:ℝ)+1)
  have hh (j : ℕ) : 1/((j:ℝ)+1)^2 ≤ H j - H (j+1) := by
    dsimp [H]
    push_cast
    field_simp
    nlinarith
  calc _ ≤ ∑ j ∈ range n, (H j-H (j+1)) := sum_le_sum (fun j _ => hh j)
       _ = H 0-H n := sum_range_sub' H n
       _ ≤ 2 := by dsimp [H]; simp; positivity

private theorem tree_nonneg (b : ℕ → ℂ) (J u : ℕ) : 0≤dyadicTreeEnergy b J u := by
  induction J generalizing u with
  | zero => exact sq_nonneg _
  | succ J ih => exact add_nonneg (add_nonneg (sq_nonneg _) (ih u)) (ih _)

private theorem long_tree_variance {ι : Type*} [Fintype ι] (Q : ℝ) (hQ : 0 < Q) (b : ι → ℕ → ℂ)
    (hb : ∀ u D : ℕ, ∑ x : ι, ‖∑ k ∈ range D, b x (u+k)‖^2 ≤ (Fintype.card ι:ℝ)*D*(1+D/Q))
    (J u : ℕ) :
    ∑ x : ι, dyadicTreeEnergy (b x) J u ≤ (Fintype.card ι:ℝ)*((J:ℝ)+1)*2^J*(1+2^J/Q) := by
  induction J generalizing u with
  | zero => simpa [dyadicTreeEnergy] using hb u 1
  | succ J ih =>
    simp only [dyadicTreeEnergy, sum_add_distrib]
    have ht := hb u (2^(J+1))
    push_cast at ht ⊢
    have hr : 1+(2:ℝ)^J/Q ≤ 1+2^(J+1)/Q := by gcongr <;> norm_num
    have hi (i : ℕ) : ∑ x : ι, dyadicTreeEnergy (b x) J i ≤
        (Fintype.card ι:ℝ)*((J:ℝ)+1)*2^J*(1+2^(J+1)/Q) :=
      (ih i).trans (mul_le_mul_of_nonneg_left hr (by positivity))
    calc _ ≤ ((Fintype.card ι:ℝ)*2^(J+1)*(1+2^(J+1)/Q) +
                (Fintype.card ι:ℝ)*((J:ℝ)+1)*2^J*(1+2^(J+1)/Q)) +
                (Fintype.card ι:ℝ)*((J:ℝ)+1)*2^J*(1+2^(J+1)/Q) :=
              add_le_add (add_le_add ht (hi u)) (hi _)
         _ = _ := by ring

private theorem long_majority_bounded_prefixes {ι : Type*} [Fintype ι] (q : ℕ) (Q : ℝ) (hQ : 0<Q) (b : ι → ℕ → ℂ)
    (hb : ∀ u D : ℕ, ∑ x : ι, ‖∑ k ∈ range D, b x (u+k)‖^2 ≤ (Fintype.card ι:ℝ)*D*(1+D/Q)) :
    ∃ G : Finset ι, 7 * Fintype.card ι ≤ 9 * G.card ∧ ∀ x ∈ G, ∀ N : ℕ, 0<N → N≤q →
      ‖∑ k ∈ range N, b x k‖^2 ≤ 18 * N * ((Nat.log 2 N:ℝ)+2)^4 * (1+2*N/Q) := by
  classical
  let w (j : ℕ) : ℝ := ((j:ℝ)+1)^3 * 2^j * (1+2^j/Q)
  have hw (j : ℕ) : 0<w j := by dsimp [w]; positivity
  let e (x : ι) := ∑ j ∈ range (q+2), dyadicTreeEnergy (b x) j 0 / w j
  have he (x : ι) : 0≤e x := sum_nonneg (fun j _ => div_nonneg (tree_nonneg _ _ _) (hw _).le)
  have hEt : ∑ x : ι, e x ≤ 2 * Fintype.card ι := by
    dsimp only [e]
    rw [sum_comm]
    calc _ ≤ ∑ j ∈ range (q+2), (Fintype.card ι:ℝ) * (1/((j:ℝ)+1)^2) := by
           apply sum_le_sum
           intro j _
           rw [← sum_div]
           apply (div_le_iff₀ (hw j)).mpr
           apply (long_tree_variance Q hQ b hb j 0).trans
           dsimp only [w]
           field_simp
           first | ring_nf | exact le_rfl
         _ = (Fintype.card ι:ℝ) * (∑ j ∈ range (q+2), 1/((j:ℝ)+1)^2) := (mul_sum ..).symm
         _ ≤ _ := by rw [mul_comm (2:ℝ)]; gcongr; exact reciprocal_square_sum _
  let bad := univ.filter (fun x : ι => 9<e x)
  have hbad : 9*(bad.card:ℝ) ≤ 2*Fintype.card ι := by
    calc _ = ∑ x ∈ bad, (9:ℝ) := by simp; ring
         _ ≤ ∑ x ∈ bad, e x := sum_le_sum (fun x hx => (mem_filter.mp hx).2.le)
         _ ≤ ∑ x : ι, e x := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => he x)
         _ ≤ _ := hEt
  refine ⟨badᶜ,?_,?_⟩
  · have hbn : 9*bad.card ≤ 2*Fintype.card ι := by exact_mod_cast hbad
    have hcard := card_add_card_compl bad
    omega
  · intro x hx N hn hnq
    have hxg : e x ≤ 9 := by
      by_contra! h
      exact (mem_compl.mp hx) (mem_filter.mpr ⟨mem_univ _,h⟩)
    let j := Nat.log 2 N + 1
    have hj : j ∈ range (q+2) := by
      apply Finset.mem_range.mpr
      have hh := Nat.log_le_self 2 N
      dsimp [j]; omega
    have hE := (single_le_sum (f := fun i => dyadicTreeEnergy (b x) i 0 / w i)
      (fun i _ => div_nonneg (tree_nonneg _ _ _) (hw _).le) hj).trans hxg
    have hEj := (div_le_iff₀ (hw j)).mp hE
    have hNpow : N ≤ 2^j := (Nat.lt_pow_succ_log_self (by decide : 1<2) N).le
    have hrec := prefix_sq_le_dyadicTreeEnergy (b x) j 0 N hNpow
    simp only [zero_add] at hrec
    have hpow : (2:ℝ)^j ≤ 2*N := by
      have h := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
      dsimp [j]; rw [pow_succ]
      exact_mod_cast (show 2 ^ Nat.log 2 N * 2 ≤ 2*N by omega)
    have hjr : (j:ℝ)+1 = (Nat.log 2 N:ℝ)+2 := by dsimp [j]; push_cast; ring
    calc _ ≤ ((j:ℝ)+1) * (9*w j) :=
              hrec.trans (mul_le_mul_of_nonneg_left hEj (by positivity))
         _ = (9*((j:ℝ)+1)^4)*2^j*(1+2^j/Q) := by dsimp [w]; ring
         _ ≤ (9*((j:ℝ)+1)^4)*(2*N)*(1+2*N/Q) := by gcongr
         _ = _ := by rw [hjr]; ring

theorem long_majority_all_prefixes {ι : Type*} [Fintype ι] (Q : ℝ) (hQ : 0<Q)
    (b : ι → ℕ → ℂ)
    (hb : ∀ u D : ℕ, ∑ x : ι, ‖∑ k ∈ range D, b x (u+k)‖^2 ≤ (Fintype.card ι:ℝ)*D*(1+D/Q)) :
    ∃ G : Finset ι, 7 * Fintype.card ι ≤ 9 * G.card ∧ ∀ x ∈ G, ∀ N : ℕ, 0<N →
      ‖∑ k ∈ range N, b x k‖^2 ≤ 18 * N * ((Nat.log 2 N:ℝ)+2)^4 * (1+2*N/Q) := by
  classical
  let ok (x : ι) (N : ℕ) := ‖∑ k ∈ range N, b x k‖^2 ≤
    18 * N * ((Nat.log 2 N:ℝ)+2)^4 * (1+2*N/Q)
  let fail (x : ι) := ∃ N : ℕ, 0<N ∧ ¬ ok x N
  let witness (x : ι) := if h : fail x then Nat.find h else 0
  let cap := univ.sup witness
  obtain ⟨G,hG,hs⟩ := long_majority_bounded_prefixes cap Q hQ b hb
  refine ⟨G,hG,?_⟩
  intro x hx N hN
  change ok x N
  by_contra hn
  have hfail : fail x := ⟨N,hN,hn⟩
  have hbad := Nat.find_spec hfail
  have hcap : Nat.find hfail ≤ cap := by
    have hwit : witness x = Nat.find hfail := dif_pos hfail
    rw [← hwit]
    exact le_sup (f:=witness) (mem_univ x)
  exact hbad.2 (hs x hx _ hbad.1 hcap)
end MasulloConductor
end

section
open Finset Complex
open scoped ComplexConjugate

private theorem residue_character_column {q : ℕ} [NeZero q] (x y : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, conj (χ x) * χ y =
      if x = y then (if IsUnit x then (Fintype.card (DirichletCharacter ℂ q) : ℂ) else 0) else 0 := by
  classical
  by_cases hx : IsUnit x
  · have hunit (χ : DirichletCharacter ℂ q) : conj (χ x) = χ x⁻¹ := by
      have hn : ‖χ x‖ = 1 := χ.unit_norm_eq_one hx.unit
      have hm : χ x⁻¹ * χ x = 1 := by
        rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit hx x).mpr rfl, map_one]
      exact (Complex.inv_eq_conj hn).symm.trans (eq_inv_of_mul_eq_one_left hm).symm
    have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    simp only [hunit, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx,if_pos hx,hcard]
  · simp [fun χ : DirichletCharacter ℂ q => χ.map_nonunit hx,hx]

private theorem moment_interval_fiber_card (q D u j : ℕ) [NeZero q] :
    let x := fun k : ℕ => ((u+k+1 : ℕ) : ZMod q)
    ((range D).filter (fun k => x k = x j)).card ≤ D/q+1 := by
  classical
  intro x
  let J := (range D).filter (fun k => x k = x j)
  have hf : Set.MapsTo (fun k : ℕ => k/q) J (range (D/q+1)) := by
    intro k hk
    have hk' : k < D := mem_range.mp (mem_filter.mp hk).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hk'.le))
  have hi : (J : Set ℕ).InjOn (fun k : ℕ => k/q) := by
    intro k hk l hl hq
    have he : x k = x l := (mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm
    have he' : (k:ZMod q) = (l:ZMod q) := by
      dsimp only [x] at he
      push_cast at he
      exact add_left_cancel (add_right_cancel he)
    have hm := (ZMod.natCast_eq_natCast_iff' k l q).mp he'
    calc
      k = k%q + q*(k/q) := (Nat.mod_add_div k q).symm
      _ = l%q + q*(l/q) := by rw [hm,show k/q=l/q from hq]
      _ = l := Nat.mod_add_div l q
  simpa only [card_range] using card_le_card_of_injOn (fun k : ℕ => k/q) hf hi

theorem MasulloRH.character_interval_second_moment_all_lengths {q : ℕ} [NeZero q]
    (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (u D : ℕ) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖∑ k ∈ range D, χ (u+k+1:ℕ) * a (u+k+1)‖^2) ≤
      (Fintype.card (DirichletCharacter ℂ q) : ℝ) * D * (1+(D:ℝ)/q) := by
  classical
  let x (k : ℕ) : ZMod q := (u+k+1:ℕ)
  let w (k : ℕ) := a (u+k+1)
  let C : ℝ := Fintype.card (DirichletCharacter ℂ q)
  let T (χ : DirichletCharacter ℂ q) (k : ℕ) := χ (x k) * w k
  let V (j k : ℕ) := (conj (w j) * w k) *
      if x j = x k then (if IsUnit (x j) then (C:ℂ) else 0) else 0
  have hnC : 0 ≤ C := Nat.cast_nonneg _
  have hv (j k : ℕ) : ‖V j k‖ ≤ if x k = x j then C else 0 := by
    by_cases h : x k = x j
    · by_cases hunit : IsUnit (x j)
      · simp only [V,if_pos h.symm,if_pos h,if_pos hunit,norm_mul,RCLike.norm_conj,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnC]
        have : ‖w j‖ * ‖w k‖ ≤ 1*1 :=
          mul_le_mul (ha _) (ha _) (norm_nonneg _) zero_le_one
        simpa using mul_le_mul_of_nonneg_right this hnC
      · simp only [V,if_pos h.symm,if_pos h,if_neg hunit,mul_zero,norm_zero]
        exact hnC
    · simp [V,h,Ne.symm h]
  have hex (χ : DirichletCharacter ℂ q) :
      conj (∑ j ∈ range D, T χ j) * ∑ k ∈ range D, T χ k =
      ∑ j ∈ range D, ∑ k ∈ range D, conj (T χ j) * T χ k := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have henergy : ((∑ χ : DirichletCharacter ℂ q, ‖∑ k ∈ range D, T χ k‖^2 : ℝ) : ℂ) =
      ∑ j ∈ range D, ∑ k ∈ range D, V j k := by
    push_cast
    simp only [← Complex.conj_mul',hex]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, (conj (w j)*w k) * (conj (χ (x j))*χ (x k)) := by
        apply Finset.sum_congr rfl; intro χ _
        simp only [T,map_mul]; ring
      _ = _ := by rw [← Finset.mul_sum,residue_character_column]; simp [V,C]
  have hrow (j : ℕ) : ‖∑ k ∈ range D, V j k‖ ≤ C * (1+(D:ℝ)/q) := by
    calc
      _ ≤ ∑ k ∈ range D, (if x k = x j then C else 0) :=
        norm_sum_le_of_le _ (fun k _ => hv j k)
      _ = ((range D).filter (fun k => x k = x j)).card * C := by rw [← Finset.sum_filter]; simp
      _ ≤ ((D / q + 1:ℕ) : ℝ) * C :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (moment_interval_fiber_card q D u j)) hnC
      _ ≤ _ := by
        rw [mul_comm C, Nat.cast_add, Nat.cast_one, add_comm (1:ℝ)]
        have hcast : ((D/q : ℕ):ℝ) ≤ (D:ℝ)/q := Nat.cast_div_le
        exact mul_le_mul_of_nonneg_right (by linarith) hnC
  change (∑ χ : DirichletCharacter ℂ q, ‖∑ k ∈ range D, T χ k‖^2) ≤ C * D * (1+(D:ℝ)/q)
  calc
    _ = ‖((∑ χ : DirichletCharacter ℂ q, ‖∑ k ∈ range D, T χ k‖^2 : ℝ):ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    _ = _ := congrArg norm henergy
    _ ≤ ∑ _j ∈ range D, C * (1+(D:ℝ)/q) := norm_sum_le_of_le _ (fun j _ => hrow j)
    _ = _ := by simp; ring
end

section
open Finset Complex
open scoped Classical

theorem solution (q : ℕ) [NeZero q] :
    let S (χ : DirichletCharacter ℂ q) (N : ℕ) :=
      ∑ k ∈ range N, χ (k+1:ℕ) * (ArithmeticFunction.moebius (k+1):ℂ)
    let H (N : ℕ) := ((Nat.log 2 N : ℝ)+2)^4
    ∃ G : Finset (DirichletCharacter ℂ q), 7*q.totient ≤ 9*G.card ∧
      7*q.totient ≤ 9*(G.erase 1).card+9 ∧
      (q.Prime → ∀ χ ∈ G.erase 1, χ.IsPrimitive) ∧
      ∀ χ ∈ G, ∀ N : ℕ, 0<N →
        ‖S χ N‖^2 ≤ 18*N*H N*(1+2*(N:ℝ)/q) ∧
        (N≤q → ‖S χ N‖^2 ≤ 54*N*H N) ∧
        (N≤q^3 → ‖S χ N‖^2 ≤ 54*(N:ℝ)^(5/3:ℝ)*H N) := by
  intro S H
  let b (χ : DirichletCharacter ℂ q) (k : ℕ) := χ (k+1:ℕ) *
    (ArithmeticFunction.moebius (k+1):ℂ)
  have hμ (n : ℕ) : ‖(ArithmeticFunction.moebius n:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))
  have hq : 0<(q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨G,hg,hb⟩ := MasulloConductor.long_majority_all_prefixes (q:ℝ) hq b
    (fun u D => MasulloRH.character_interval_second_moment_all_lengths
      (q:=q) (fun n => (ArithmeticFunction.moebius n:ℂ)) hμ u D)
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [hcard] at hg
  refine ⟨G,hg,?_,?_,?_⟩
  · rw [card_erase_eq_ite]
    split_ifs <;> omega
  · intro hp χ hχ
    have hne : χ ≠ 1 := ne_of_mem_erase hχ
    exact ((Nat.dvd_prime hp).mp χ.conductor_dvd_level).resolve_left
      (fun h => hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · intro χ hχ N hn
    have hbound : ‖S χ N‖^2 ≤ 18*N*H N*(1+2*(N:ℝ)/q) := hb χ hχ N hn
    have hnreal : 0<(N:ℝ) := Nat.cast_pos.mpr hn
    have hone : 1≤(N:ℝ) := by exact_mod_cast hn
    have hH : 0≤H N := by dsimp [H]; positivity
    refine ⟨hbound,?_,?_⟩
    · intro hnq
      have hrat : 2*(N:ℝ)/q ≤ 2 := (div_le_iff₀ hq).mpr (by exact_mod_cast (Nat.mul_le_mul_left 2 hnq))
      calc _ ≤ _ := hbound
           _ ≤ 18*N*H N*3 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
           _ = _ := by ring
    · intro hnq
      have hNq : (N:ℝ) ≤ (q:ℝ)^3 := by exact_mod_cast hnq
      have hroot : (N:ℝ)^(1/3:ℝ) ≤ (q:ℝ) := by
        calc _ ≤ ((q:ℝ)^(3:ℝ))^(1/3:ℝ) :=
                  Real.rpow_le_rpow hnreal.le (by simpa using hNq) (by norm_num)
             _ = _ := by rw [← Real.rpow_mul hq.le]; norm_num
      have hpow : (N:ℝ)^(1/3:ℝ)*(N:ℝ)^(2/3:ℝ) = N := by
        rw [← Real.rpow_add hnreal]; norm_num
      have hrat : (N:ℝ)/q ≤ (N:ℝ)^(2/3:ℝ) := by
        apply (div_le_iff₀ hq).mpr
        calc (N:ℝ) = (N:ℝ)^(1/3:ℝ)*(N:ℝ)^(2/3:ℝ) := hpow.symm
             _ ≤ (q:ℝ)*((N:ℝ)^(2/3:ℝ)) :=
                  mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hnreal.le _)
             _ = _ := mul_comm _ _
      have hp1 : 1 ≤ (N:ℝ)^(2/3:ℝ) := Real.one_le_rpow hone (by norm_num)
      calc _ ≤ _ := hbound
           _ ≤ 18*N*H N*(3*(N:ℝ)^(2/3:ℝ)) := by
             apply mul_le_mul_of_nonneg_left _ (by positivity)
             rw [mul_div_assoc]; linarith
           _ = 54*((N:ℝ)*(N:ℝ)^(2/3:ℝ))*H N := by ring
           _ = _ := by
             conv_lhs => arg 1; arg 2; arg 1; rw [← Real.rpow_one (N:ℝ)]
             rw [← Real.rpow_add hnreal]
             norm_num
end
