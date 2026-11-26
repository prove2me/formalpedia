-- Prove2me | solution 1 for Erdos266.lattice_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:43:44.18887+00:00
-- url     : https://prove2.me/submissions/ee05e42e-e123-4f75-9c12-a714895628de

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma
public import Theorems.Thm_Erdos266_exists_round_toward_zero
public import Theorems.Thm_Erdos266_abs_mulVec_le
public import Theorems.Thm_Erdos266_det_latticeMatrix_ne_zero
public import Theorems.Thm_Erdos266_slope_lemma


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix
set_option maxHeartbeats 3200000
namespace Erdos266
theorem _root_.solution (d : ℕ) :
    ∃ ε D : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ D ∧
      ∀ (N M : ℕ), 1 ≤ N → 4 * d * M ≤ N →
      ∀ x : Fin d → ℝ,
        (∀ i : Fin d, |x i - ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ)|
          ≤ ε * M / (N : ℝ) ^ (i.val + 2)) →
        ∃ n : Fin d → ℤ, (∀ j, |n j| ≤ (M : ℤ)) ∧
          ∀ i : Fin d,
            |x i - ∑ j : Fin d, f (i.val + 1) ((((j.val + 1) * N : ℕ) : ℝ) + (n j : ℝ))|
              ≤ D * (1 / (N : ℝ) ^ (i.val + 2) + (M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3)) := by
  classical
  -- slope-lemma constants for levels 1..d
  choose C hC0 hC using fun i : Fin d => slope_lemma (i.val + 1) (Nat.le_add_left 1 i.val)
  set W := latticeMatrix d with hWdef
  have hdet : W.det ≠ 0 := det_latticeMatrix_ne_zero d
  set v : ℤ := |W.det| with hvdef
  have hv0 : (0 : ℤ) < v := abs_pos.mpr hdet
  have hv1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv0
  have hvR : (0 : ℝ) < (v : ℝ) := by linarith
  set R : ℝ := ∑ p : Fin d × Fin d, |((W.adjugate p.1 p.2 : ℤ) : ℝ)| with hRdef
  have hR0 : (0 : ℝ) ≤ R := sum_nonneg fun _ _ => abs_nonneg _
  set K : ℝ := (d : ℝ) ^ (d + 1) * (R + 1) * (v : ℝ) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    have h1 : (0:ℝ) ≤ (d : ℝ) ^ (d + 1) := by positivity
    exact mul_nonneg (mul_nonneg h1 (by linarith)) (by linarith)
  have hKv : (0 : ℝ) < K + v := by linarith
  set ε : ℝ := (v : ℝ) / (K + (v : ℝ)) with hεdef
  set D : ℝ := (d : ℝ) * v + (d : ℝ) * (∑ i : Fin d, C i) + 1 with hDdef
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one hKv]
    linarith
  have hCsum0 : (0:ℝ) ≤ ∑ i : Fin d, C i := sum_nonneg fun i _ => (hC0 i).le
  have hD1 : 1 ≤ D := by
    have h1 : (0:ℝ) ≤ (d : ℝ) * v := by positivity
    have h2 : (0:ℝ) ≤ (d : ℝ) * (∑ i : Fin d, C i) :=
      mul_nonneg (Nat.cast_nonneg d) hCsum0
    rw [hDdef]
    linarith
  refine ⟨ε, D, hε0, hε1, hD1, ?_⟩
  intro N M hN1 hNM x hx
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hM0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  have hεM : (0:ℝ) ≤ ε * M := mul_nonneg hε0.le hM0
  -- the anchor and the normalized targets
  set s : Fin d → ℝ :=
    fun i => ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ) with hsdef
  set u : Fin d → ℝ :=
    fun i => (s i - x i) * (N : ℝ) ^ (i.val + 2) / ((i.val : ℝ) + 1) with hudef
  have hu_bound : ∀ i, |u i| ≤ ε * M := by
    intro i
    have h1 : |s i - x i| ≤ ε * M / (N : ℝ) ^ (i.val + 2) := by
      rw [abs_sub_comm]
      exact hx i
    have hIpos : (0:ℝ) < (i.val : ℝ) + 1 := by positivity
    have e1 : |u i| = |s i - x i| * (N:ℝ)^(i.val+2) / ((i.val:ℝ)+1) := by
      simp only [hudef]
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hNR, abs_of_pos hIpos]
    rw [e1]
    calc |s i - x i| * (N:ℝ)^(i.val+2) / ((i.val:ℝ)+1)
        ≤ (ε * M / (N:ℝ)^(i.val+2)) * (N:ℝ)^(i.val+2) / ((i.val:ℝ)+1) := by gcongr
    _ = ε * M / ((i.val:ℝ)+1) := by field_simp
    _ ≤ ε * M := div_le_self hεM (by linarith)
  -- round each target toward zero to a multiple of `v`
  choose z hz1 hz2 using fun i => exists_round_toward_zero (u i) hvR
  have hzb : ∀ i, |(z i : ℝ)| ≤ ε * M / v := by
    intro i
    rw [le_div_iff₀ hvR]
    have h1 := hz2 i
    have h2 := hu_bound i
    linarith [mul_comm ((v:ℤ):ℝ) |(z i : ℝ)|]
  -- exact integer preimage via the adjugate
  set z' : Fin d → ℤ := fun i => if 0 ≤ W.det then z i else -(z i) with hz'def
  set m : Fin d → ℤ := W.adjugate.mulVec z' with hmdef
  set n : Fin d → ℤ := fun j => ((j : ℤ) + 1) ^ (d + 1) * m j with hndef
  have hsolve : ∀ i, ((W.mulVec m) i : ℤ) = v * z i := by
    have hWm : W.mulVec m = W.det • z' := by
      rw [hmdef, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
    intro i
    rw [hWm, Pi.smul_apply, smul_eq_mul]
    simp only [hz'def]
    split_ifs with h
    · rw [hvdef, abs_of_nonneg h]
    · rw [hvdef, abs_of_neg (lt_of_not_ge h)]
      ring
  have hz'b : ∀ i, |(z' i : ℝ)| ≤ ε * M / v := by
    intro i
    simp only [hz'def]
    split_ifs
    · exact hzb i
    · rw [Int.cast_neg, abs_neg]
      exact hzb i
  have hm_bound : ∀ j, |(m j : ℝ)| ≤ R * (ε * M / v) := by
    intro j
    have := abs_mulVec_le W.adjugate z' hz'b j
    rw [← hRdef] at this
    exact this
  -- the block shifts stay in the required range
  have hn_bound_real : ∀ j, |(n j : ℝ)| ≤ (M : ℝ) := by
    intro j
    have hj1 : |((j : ℤ) : ℝ) + 1| ≤ (d : ℝ) := by
      rw [abs_of_pos (by positivity)]
      exact_mod_cast j.isLt
    have e1 : |(n j : ℝ)| = |((j : ℤ) : ℝ) + 1| ^ (d + 1) * |(m j : ℝ)| := by
      simp only [hndef]
      push_cast
      rw [abs_mul, abs_pow]
    rw [e1]
    have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    calc |((j:ℤ):ℝ) + 1| ^ (d+1) * |(m j : ℝ)|
        ≤ (d:ℝ)^(d+1) * (R * (ε * M / v)) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hj1 _) (hm_bound j)
            (abs_nonneg _) (by positivity)
    _ = ((d:ℝ)^(d+1) * R) * ((M:ℝ)/(K+v)) := by
          rw [hεdef]
          field_simp
    _ ≤ (K + v) * ((M:ℝ)/(K+v)) := by
          have hKvR : (d:ℝ)^(d+1)*R ≤ K + v := by
            rw [hKdef]
            have h1 : (0:ℝ) ≤ (d:ℝ)^(d+1) := by positivity
            nlinarith
          exact mul_le_mul_of_nonneg_right hKvR (by positivity)
    _ = M := by field_simp
  have hn_bound : ∀ j, |n j| ≤ (M : ℤ) := by
    intro j
    have := hn_bound_real j
    rw [← Int.cast_abs] at this
    exact_mod_cast this
  refine ⟨n, hn_bound, ?_⟩
  intro i
  have hI_le_d : (i.val : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast i.isLt
  have hNk2 : (0:ℝ) < (N:ℝ)^(i.val+2) := by positivity
  -- the linear term sums to the lattice point
  have hjN : ∀ j : Fin d, (((j.val + 1) * N : ℕ) : ℝ) = ((j.val : ℝ) + 1) * N := by
    intro j
    push_cast
    ring
  have hLinSum : ∑ j : Fin d,
        ((i.val:ℝ)+1) * (n j : ℝ) / ((((j.val+1)*N : ℕ):ℝ))^(i.val+2)
      = ((i.val:ℝ)+1) * ((v * z i : ℤ) : ℝ) / (N:ℝ)^(i.val+2) := by
    have hWmi : ((W.mulVec m i : ℤ) : ℝ)
        = ∑ j : Fin d, ((j.val:ℝ)+1)^(d-1-i.val) * (m j : ℝ) := by
      rw [Matrix.mulVec, dotProduct]
      simp only [hWdef, latticeMatrix, Matrix.of_apply]
      push_cast
      rfl
    rw [← hsolve i, hWmi, Finset.mul_sum, Finset.sum_div]
    refine sum_congr rfl fun j _ => ?_
    have hj0 : (0:ℝ) < (j.val : ℝ) + 1 := by positivity
    have hpow : ((j.val:ℝ)+1)^(d+1)
        = ((j.val:ℝ)+1)^(d-1-i.val) * ((j.val:ℝ)+1)^(i.val+2) := by
      rw [← pow_add]
      congr 1
      omega
    have hn_cast : (n j : ℝ) = ((j.val:ℝ)+1)^(d+1) * (m j : ℝ) := by
      simp only [hndef]
      push_cast
      ring
    rw [hn_cast, hjN j, mul_pow, hpow]
    field_simp
  -- distance from the lattice point to the target displacement
  have happrox : |((i.val:ℝ)+1) * ((v * z i : ℤ) : ℝ) / (N:ℝ)^(i.val+2) - (s i - x i)|
      ≤ (d:ℝ) * v / (N:ℝ)^(i.val+2) := by
    have hIne : ((i.val:ℝ)+1) ≠ 0 := by positivity
    have hsx : s i - x i = ((i.val:ℝ)+1) * u i / (N:ℝ)^(i.val+2) := by
      simp only [hudef]
      field_simp
    rw [hsx]
    have e1 : ((i.val:ℝ)+1) * ((v * z i : ℤ):ℝ)/(N:ℝ)^(i.val+2)
          - ((i.val:ℝ)+1) * u i/(N:ℝ)^(i.val+2)
        = (((i.val:ℝ)+1)/(N:ℝ)^(i.val+2)) * (((v:ℤ):ℝ) * ((z i : ℤ):ℝ) - u i) := by
      push_cast
      ring
    rw [e1, abs_mul, abs_div, abs_of_pos (show (0:ℝ) < (i.val:ℝ)+1 by positivity),
      abs_of_pos hNk2]
    calc ((i.val:ℝ)+1)/(N:ℝ)^(i.val+2) * |((v:ℤ):ℝ) * ((z i : ℤ):ℝ) - u i|
        ≤ ((d:ℝ))/(N:ℝ)^(i.val+2) * (v:ℝ) := by
          gcongr
          exact hz1 i
    _ = (d:ℝ) * v / (N:ℝ)^(i.val+2) := by ring
  -- the slope errors
  have hslope : ∀ j : Fin d,
      |f (i.val+1) (((j.val+1)*N : ℕ):ℝ)
          - f (i.val+1) ((((j.val+1)*N : ℕ):ℝ) + (n j : ℝ))
          - ((i.val:ℝ)+1) * (n j : ℝ) / ((((j.val+1)*N : ℕ):ℝ))^(i.val+2)|
        ≤ C i * (M:ℝ)^2 / (N:ℝ)^(i.val+3) := by
    intro j
    have hyp : 4 * ((i.val+1 : ℕ) : ℝ) * |((n j : ℤ) : ℝ)| ≤ (((j.val+1)*N : ℕ) : ℝ) := by
      rw [hjN j]
      have h1 : |((n j : ℤ) : ℝ)| ≤ (M:ℝ) := hn_bound_real j
      have h2 : (4 * d * M : ℝ) ≤ (N:ℝ) := by exact_mod_cast hNM
      have h3 : ((i.val:ℝ)+1) ≤ (d:ℝ) := hI_le_d
      have h4 : (N:ℝ) ≤ ((j.val:ℝ)+1) * N := by
        have hj : (0:ℝ) ≤ (j.val:ℝ) := Nat.cast_nonneg _
        nlinarith
      have h5 : 4 * ((i.val+1 : ℕ) : ℝ) * |((n j : ℤ) : ℝ)| ≤ 4 * (d:ℝ) * M := by
        push_cast
        have habs0 : (0:ℝ) ≤ |((n j : ℤ) : ℝ)| := abs_nonneg _
        nlinarith
      linarith
    have happ := hC i ((j.val+1)*N) (n j) hyp
    have e2 : i.val + 1 + 1 = i.val + 2 := rfl
    have e3 : i.val + 1 + 2 = i.val + 3 := rfl
    rw [e2, e3] at happ
    simp only [Nat.cast_add, Nat.cast_one] at happ
    refine happ.trans ?_
    have hjN1 : (N:ℝ) ≤ (((j.val+1)*N : ℕ) : ℝ) := by
      rw [hjN j]
      have hj : (0:ℝ) ≤ (j.val:ℝ) := Nat.cast_nonneg _
      nlinarith
    have hn2 : ((n j : ℤ):ℝ)^2 ≤ (M:ℝ)^2 := by
      have h1 : |((n j : ℤ) : ℝ)| ≤ (M:ℝ) := hn_bound_real j
      have h2 : -(M:ℝ) ≤ ((n j : ℤ):ℝ) ∧ ((n j : ℤ):ℝ) ≤ (M:ℝ) := abs_le.mp h1
      nlinarith [h2.1, h2.2]
    gcongr <;>
      first
        | exact mul_nonneg (hC0 i).le (by positivity)
        | exact (hC0 i).le
  -- assemble
  have hsplit : x i - ∑ j : Fin d, f (i.val+1) ((((j.val+1)*N : ℕ):ℝ) + (n j : ℝ))
      = (((i.val:ℝ)+1) * ((v * z i : ℤ) : ℝ) / (N:ℝ)^(i.val+2) - (s i - x i))
        + ∑ j : Fin d, (f (i.val+1) (((j.val+1)*N : ℕ):ℝ)
            - f (i.val+1) ((((j.val+1)*N : ℕ):ℝ) + (n j : ℝ))
            - ((i.val:ℝ)+1) * (n j : ℝ) / ((((j.val+1)*N : ℕ):ℝ))^(i.val+2)) := by
    rw [sum_sub_distrib, sum_sub_distrib, ← hLinSum]
    have : s i = ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ) := by
      rw [hsdef]
    rw [← this]
    ring
  rw [hsplit]
  calc |(((i.val:ℝ)+1) * ((v * z i : ℤ) : ℝ) / (N:ℝ)^(i.val+2) - (s i - x i))
        + ∑ j : Fin d, (f (i.val+1) (((j.val+1)*N : ℕ):ℝ)
            - f (i.val+1) ((((j.val+1)*N : ℕ):ℝ) + (n j : ℝ))
            - ((i.val:ℝ)+1) * (n j : ℝ) / ((((j.val+1)*N : ℕ):ℝ))^(i.val+2))|
      ≤ (d:ℝ) * v / (N:ℝ)^(i.val+2) + ∑ _j : Fin d, C i * (M:ℝ)^2 / (N:ℝ)^(i.val+3) := by
        refine (abs_add_le _ _).trans (add_le_add happrox ?_)
        refine (abs_sum_le_sum_abs _ _).trans ?_
        exact sum_le_sum fun j _ => hslope j
  _ = (d:ℝ) * v / (N:ℝ)^(i.val+2) + (d:ℝ) * (C i * (M:ℝ)^2 / (N:ℝ)^(i.val+3)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  _ ≤ D * (1 / (N : ℝ) ^ (i.val + 2) + (M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3)) := by
        have hdv : (d:ℝ) * v ≤ D := by
          have h2 : (0:ℝ) ≤ (d : ℝ) * (∑ i : Fin d, C i) :=
            mul_nonneg (Nat.cast_nonneg d) hCsum0
          rw [hDdef]
          linarith
        have hdC : (d:ℝ) * C i ≤ D := by
          have h1 : C i ≤ ∑ i' : Fin d, C i' :=
            single_le_sum (fun i' _ => (hC0 i').le) (mem_univ i)
          have h2 : (d:ℝ) * C i ≤ (d:ℝ) * (∑ i' : Fin d, C i') :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
          have h3 : (0:ℝ) ≤ (d:ℝ) * v := by positivity
          rw [hDdef]
          linarith
        have hNk3 : (0:ℝ) < (N:ℝ)^(i.val+3) := by positivity
        rw [mul_add]
        refine add_le_add ?_ ?_
        · rw [mul_one_div]
          exact div_le_div_of_nonneg_right hdv hNk2.le
        · have e4 : (d:ℝ) * (C i * (M:ℝ)^2 / (N:ℝ)^(i.val+3))
              = ((d:ℝ) * C i) * ((M:ℝ)^2 / (N:ℝ)^(i.val+3)) := by ring
          have e5 : D * ((M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3))
              = D * ((M:ℝ)^2 / (N:ℝ)^(i.val+3)) := rfl
          rw [e4]
          exact mul_le_mul_of_nonneg_right hdC (by positivity)
end Erdos266
