-- Prove2me | solution 1 for GRH.dirichlet_nonzero_of_weighted_prefix_cover
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:17:01.304324+00:00
-- url     : https://prove2.me/submissions/056c35a8-a998-446a-b7f5-ac76155406b0

import Definitions.Def_GRH_DirichletPrefix
import Theorems.Thm_GRH_dirichlet_prefix_unit_count_bound
import Theorems.Thm_GRH_dirichlet_abel_disk_from_centered_prefixes
import Theorems.Thm_GlobalTheory_DirichletTail_norm_cpow_sub_le
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open GRH.DirichletPrefix Complex

private lemma prefix_expansion (a w : ℕ → ℂ) (h1 : w 0=1) (M : ℕ) :
    (∑ k ∈ Finset.range M,a k*w k) + (1-∑ k ∈ Finset.range M,a k)*w M - 1 =
      ∑ k ∈ Finset.range M, ((∑ j ∈ Finset.range (k+1),a j)-1)*(w k-w (k+1)) := by
  induction M with
  | zero => simp [h1]
  | succ M ih =>
    rw [Finset.sum_range_succ (f:=fun k => ((∑ j ∈ Finset.range (k+1),a j)-1)*(w k-w (k+1)))]
    rw [← ih]
    simp only [Finset.sum_range_succ]
    ring

private lemma at_period (Q M R : ℕ) [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hp : ψ ≠ 1)
    (s : ℂ) (x K : ℝ) (hx : 0 < x) (hxs : x ≤ s.re) (hK : ‖s‖/x ≤ K)
    (hR : ∀ r : Fin Q, weightAt Q r.val ≤ R) :
    ‖ψ.LFunction s-1‖ ≤ K*error Q M R x := by
  let A (k : ℕ) := ψ ((k+1:ℕ):ZMod Q)
  let w (k : ℕ) := ((k+1:ℕ):ℂ)^(-s)
  let u (k : ℕ) := ((k:ℝ)+1)^(-x)
  let P := (∑ k ∈ Finset.range M,A k*w k)+(1-∑ k ∈ Finset.range M,A k)*w M
  have sx := hx.trans_le hxs
  have kpos := (div_nonneg (norm_nonneg s) hx.le).trans hK
  have disk (n : ℕ) : ‖(∑ k ∈ Finset.range n,A k)-1‖ ≤ (weight Q n:ℝ) :=
    GRH.dirichlet_prefix_unit_count_bound Q ψ hp n
  have tail := GRH.dirichlet_abel_disk_from_centered_prefixes Q ψ hp M 1 R (by positivity)
    (fun n _ => (disk n).trans (by exact_mod_cast hR ⟨n%Q,Nat.mod_lt _ (NeZero.pos Q)⟩)) s sx
  change ‖ψ.LFunction s-P‖ ≤ _ at tail
  have rat := (div_le_div_of_nonneg_left (norm_nonneg s) hx hxs).trans hK
  have mono := Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ (M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M]) (neg_le_neg hxs)
  have tail' : ‖ψ.LFunction s-P‖ ≤ (R:ℝ)*K*u M := tail.trans
    (mul_le_mul (mul_le_mul_of_nonneg_left rat (by positivity)) mono (by positivity)
      (mul_nonneg (by positivity) kpos))
  have diff (k : ℕ) : ‖w k-w (k+1)‖ ≤ K*(u k-u (k+1)) := by
    have he := GlobalTheory.DirichletTail.norm_cpow_sub_le (s:=s) (a:=(k:ℝ)+1)
      (b:=(k:ℝ)+1+1) (δ:=x) (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (by linarith) hx hxs
    have variation : ‖w k-w (k+1)‖ ≤ (‖s‖/x)*(u k-u (k+1)) := by
      simpa [w,u] using he
    apply variation.trans (mul_le_mul_of_nonneg_right hK _)
    apply sub_nonneg.mpr
    dsimp [u]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hx.le)
    push_cast
    linarith
  have finite : ‖P-1‖ ≤ K * ∑ k ∈ Finset.range M,(weight Q (k+1):ℝ)*(u k-u (k+1)) := by
    dsimp only [P]
    rw [prefix_expansion A w (by simp [w]),Finset.mul_sum]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum _)
    intro k _
    rw [norm_mul]
    have h := mul_le_mul (disk (k+1)) (diff k) (norm_nonneg _) (Nat.cast_nonneg _)
    linarith only [h]
  have tri := norm_sub_le_norm_sub_add_norm_sub (ψ.LFunction s) P 1
  apply tri.trans
  dsimp [error]
  have e (k : ℕ) : u (k+1)=((k:ℝ)+2)^(-x) := by simp [u]; ring_nf
  simp only [e] at finite
  dsimp only [u] at finite tail'
  linarith only [finite,tail']

/-- A weighted periodic prefix certificate excludes all nonprincipal
character zeros on the entire rectangle at every divisor level. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (a b H : ℝ) (hw : Covers d a b H)
    (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) (ht : |s.im| ≤ H) : χ.LFunction s ≠ 0 := by
  obtain ⟨Q,M,R,x,K,hQ,hd,hx,hxa,hK,hrect,hR,hcheck⟩ := hw
  let : NeZero Q := ⟨by omega⟩
  let ψ := DirichletCharacter.changeLevel hd χ
  have hp : ψ ≠ 1 := fun e => hχ ((DirichletCharacter.changeLevel_eq_one_iff hd).1 e)
  have hxs := hxa.trans ha
  have norm_bound : ‖s‖ ≤ K*x := by
    have re := mul_self_le_mul_self (hx.le.trans hxs) hb
    have im := mul_self_le_mul_self (abs_nonneg _) ht
    rw [← sq, sq_abs] at im
    nlinarith [Complex.sq_norm_sub_sq_re s, mul_nonneg hK hx.le, norm_nonneg s]
  have est := at_period Q M R ψ hp s x K hx hxs ((div_le_iff₀ hx).2 norm_bound) hR
  intro hz
  have ez := DirichletCharacter.LFunction_changeLevel hd χ (s:=s) (.inl hχ)
  rw [hz,zero_mul] at ez
  have strict := est.trans_lt hcheck
  change ‖(DirichletCharacter.changeLevel hd χ).LFunction s - 1‖ < 1 at strict
  simp [ez] at strict
