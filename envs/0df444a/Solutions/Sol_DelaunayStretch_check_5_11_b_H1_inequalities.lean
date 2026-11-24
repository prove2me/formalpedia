-- Prove2me | solution 1 for DelaunayStretch.check_5_11_b_H1_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T04:12:42.51683+00:00
-- url     : https://prove2.me/submissions/5426642d-a7a6-460b-b089-43d5955b74fc

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients
open DelaunayStretch

namespace CheckBD

/-! ## Part 1. Cubic B-splines: local polynomial pieces, nonnegativity, partition of unity -/

/-- Polynomials in one variable as coefficient lists (lowest degree first). -/
def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

/-- `(a + b s) * p`. -/
def pmulLin (a b : ℚ) (p : List ℚ) : List ℚ := padd (p.map (a * ·)) (0 :: p.map (b * ·))

/-- Evaluation of a coefficient list at a real point (Horner). -/
noncomputable def peval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: p, s => (c : ℝ) + s * peval p s

lemma peval_padd : ∀ (p q : List ℚ) (s : ℝ), peval (padd p q) s = peval p s + peval q s
  | [], q, s => by simp [padd, peval]
  | a :: p, [], s => by simp [padd, peval]
  | a :: p, b :: q, s => by
      simp only [padd, peval, peval_padd p q s]; push_cast; ring

lemma peval_map (a : ℚ) : ∀ (p : List ℚ) (s : ℝ), peval (p.map (a * ·)) s = a * peval p s
  | [], s => by simp [peval]
  | c :: p, s => by
      simp only [List.map_cons, peval, peval_map a p s]; push_cast; ring

lemma peval_pmulLin (a b : ℚ) (p : List ℚ) (s : ℝ) :
    peval (pmulLin a b p) s = ((a : ℝ) + b * s) * peval p s := by
  simp only [pmulLin, peval_padd, peval, peval_map]; push_cast; ring

/-- Rational copy of `splineKnot`. -/
def knotQ (j : ℕ) : ℚ := max 0 (min 1 (((j : ℚ) - 3) / 32))

lemma knotQ_cast (j : ℕ) : ((knotQ j : ℚ) : ℝ) = splineKnot j := by
  simp [knotQ, splineKnot]

/-- The polynomial (in the local variable `s = 32 τ - k`) representing the B-spline
`N_{j,p}` on the knot interval `[k/32, (k+1)/32]`. -/
def bpoly (k : ℕ) : ℕ → ℕ → List ℚ
  | 0, j => [if j = k + 3 then 1 else 0]
  | p + 1, j =>
      padd (pmulLin (((k : ℚ) / 32 - knotQ j) / (knotQ (j + p + 1) - knotQ j))
                    ((1 / 32) / (knotQ (j + p + 1) - knotQ j)) (bpoly k p j))
           (pmulLin ((knotQ (j + p + 2) - (k : ℚ) / 32) / (knotQ (j + p + 2) - knotQ (j + 1)))
                    ((-1 / 32) / (knotQ (j + p + 2) - knotQ (j + 1))) (bpoly k p (j + 1)))

lemma splineKnot_mono {i j : ℕ} (h : i ≤ j) : splineKnot i ≤ splineKnot j := by
  unfold splineKnot
  have : ((i : ℝ) - 3) / 32 ≤ ((j : ℝ) - 3) / 32 := by
    have : (i : ℝ) ≤ j := by exact_mod_cast h
    linarith
  exact max_le_max le_rfl (min_le_min le_rfl this)

lemma splineKnot_le_one (j : ℕ) : splineKnot j ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma splineKnot_k3 (k : ℕ) (hk : k ≤ 32) : splineKnot (k + 3) = (k : ℝ) / 32 := by
  unfold splineKnot
  have h1 : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  rw [show ((k : ℝ) + 3 - 3) / 32 = (k : ℝ) / 32 by ring]
  rw [min_eq_right (by linarith), max_eq_right (by positivity)]

lemma splineKnot_k4 (k : ℕ) (hk : k ≤ 31) : splineKnot (k + 3 + 1) = ((k : ℝ) + 1) / 32 := by
  have := splineKnot_k3 (k + 1) (by omega)
  rw [show k + 3 + 1 = k + 1 + 3 by ring, this]; push_cast; ring

lemma deg0_local (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) (j : ℕ) :
    bsplineDeg0 j τ = if j = k + 3 then 1 else 0 := by
  have hk' : (k : ℝ) ≤ 31 := by exact_mod_cast hk
  unfold bsplineDeg0
  by_cases hj : j = k + 3
  · subst hj
    rw [if_pos rfl, if_pos]
    rcases h1 with h1 | ⟨h31, hτ⟩
    · left
      rw [splineKnot_k3 k (by omega), splineKnot_k4 k hk]
      exact ⟨h0, h1⟩
    · right; exact ⟨by omega, hτ⟩
  · rw [if_neg hj, if_neg]
    rintro (⟨ha, hb⟩ | ⟨hj34, hτ⟩)
    · rcases h1 with h1 | ⟨h31, hτ⟩
      · rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · have := splineKnot_mono (show j + 1 ≤ k + 3 by omega)
          rw [splineKnot_k3 k (by omega)] at this
          linarith
        · have := splineKnot_mono (show k + 3 + 1 ≤ j by omega)
          rw [splineKnot_k4 k hk] at this
          linarith
      · have := splineKnot_le_one (j + 1)
        linarith
    · rcases h1 with h1 | ⟨h31, hτ'⟩
      · linarith
      · omega

lemma basis_local (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) :
    ∀ p j, bsplineBasis p j τ = peval (bpoly k p j) (32 * τ - k)
  | 0, j => by
      rw [bsplineBasis, deg0_local k hk τ h0 h1 j]
      simp only [bpoly, peval]
      split_ifs <;> simp
  | p + 1, j => by
      rw [bsplineBasis, bpoly, peval_padd, peval_pmulLin, peval_pmulLin,
        ← basis_local k hk τ h0 h1 p j, ← basis_local k hk τ h0 h1 p (j + 1)]
      push_cast [knotQ_cast]
      ring

lemma peval_bpoly_zero (k : ℕ) (s : ℝ) : ∀ p j, k + 3 < j → peval (bpoly k p j) s = 0
  | 0, j, hj => by
      simp only [bpoly, peval]
      rw [if_neg (by omega)]; simp
  | p + 1, j, hj => by
      rw [bpoly, peval_padd, peval_pmulLin, peval_pmulLin, peval_bpoly_zero k s p j hj,
        peval_bpoly_zero k s p (j + 1) (by omega)]
      ring

lemma peval_bpoly_zero_low (k : ℕ) (s : ℝ) : ∀ p j, j + p < k + 3 → peval (bpoly k p j) s = 0
  | 0, j, hj => by
      simp only [bpoly, peval]
      rw [if_neg (by omega)]; simp
  | p + 1, j, hj => by
      rw [bpoly, peval_padd, peval_pmulLin, peval_pmulLin,
        peval_bpoly_zero_low k s p j (by omega), peval_bpoly_zero_low k s p (j + 1) (by omega)]
      ring
lemma exists_interval (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∃ k : ℕ, k ≤ 31 ∧ (k : ℝ) / 32 ≤ τ ∧ (τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) := by
  by_cases hτ : τ = 1
  · refine ⟨31, le_rfl, ?_, Or.inr ⟨rfl, hτ⟩⟩
    rw [hτ]; norm_num
  · have hlt : τ < 1 := lt_of_le_of_ne h1 hτ
    have hf1 := Nat.floor_le (show (0 : ℝ) ≤ 32 * τ by linarith)
    have hf2 := Nat.lt_floor_add_one (32 * τ)
    refine ⟨⌊32 * τ⌋₊, ?_, ?_, Or.inl ?_⟩
    · have : (⌊32 * τ⌋₊ : ℝ) < 32 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    · linarith
    · linarith

lemma local_s_bounds (k : ℕ) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) :
    0 ≤ 32 * τ - k ∧ 32 * τ - k ≤ 1 := by
  constructor
  · linarith
  · rcases h1 with h1 | ⟨h31, hτ⟩
    · linarith
    · subst h31; rw [hτ]; norm_num


/-! ## Part 2. A spline on one knot interval as an explicit rational polynomial -/

/-- Coefficient `c_j`, extended by `0` outside `0 ≤ j < 35`. -/
def cN (c : Fin 35 → ℚ) (j : ℕ) : ℚ := if h : j < 35 then c ⟨j, h⟩ else 0

/-- `Σ_{d<4} c_{k+d} N_{k+d}` on the knot interval `k`, in the local variable `s = 32τ − k`. -/
def splineQ (c : Fin 35 → ℚ) (k : ℕ) : List ℚ :=
  padd (padd (padd ((bpoly k 3 k).map (cN c k * ·)) ((bpoly k 3 (k + 1)).map (cN c (k + 1) * ·)))
    ((bpoly k 3 (k + 2)).map (cN c (k + 2) * ·))) ((bpoly k 3 (k + 3)).map (cN c (k + 3) * ·))

/-- Composition `p(a + b x)`. -/
def pcompLin (a b : ℚ) : List ℚ → List ℚ
  | [] => []
  | c :: p => padd [c] (pmulLin a b (pcompLin a b p))

lemma peval_pcompLin (a b : ℚ) : ∀ (p : List ℚ) (x : ℝ),
    peval (pcompLin a b p) x = peval p ((a : ℝ) + b * x)
  | [], x => by simp [pcompLin, peval]
  | c :: p, x => by
      rw [pcompLin, peval_padd, peval_pmulLin, peval_pcompLin a b p x]
      simp [peval]

lemma spline_local (c : Fin 35 → ℚ) (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) :
    ∑ l : Fin 35, (c l : ℝ) * bspline l τ = peval (splineQ c k) (32 * τ - k) := by
  have e1 : ∑ l : Fin 35, (c l : ℝ) * bspline l τ =
      ∑ l ∈ Finset.range 35, (cN c l : ℝ) * bspline l τ := by
    rw [← Fin.sum_univ_eq_sum_range (fun l => (cN c l : ℝ) * bspline l τ) 35]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [cN, l.2]
  rw [e1]
  simp only [bspline, basis_local k hk τ h0 h1]
  rw [← Finset.sum_subset (s₁ := Finset.Ico k (k + 4))]
  · rw [Finset.sum_Ico_eq_sum_range, show k + 4 - k = 4 by omega]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
    simp only [splineQ, peval_padd, peval_map]
  · intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
    rcases hx with hx | hx
    · rw [peval_bpoly_zero_low k _ 3 x (by omega)]; ring
    · rw [peval_bpoly_zero k _ 3 x (by omega)]; ring

/-! ## Part 3. Integer polynomials and pointwise Taylor models -/

def iadd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: iadd p q

def ismul (a : ℤ) (p : List ℤ) : List ℤ := p.map (fun b => a * b)

def imul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => iadd (ismul a q) (0 :: imul p q)

def inorm : List ℤ → ℕ
  | [] => 0
  | a :: p => a.natAbs + inorm p

noncomputable def ipev : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, v => (a : ℝ) + v * ipev p v

lemma ipev_iadd : ∀ (p q : List ℤ) (v : ℝ), ipev (iadd p q) v = ipev p v + ipev q v
  | [], q, v => by simp [iadd, ipev]
  | a :: p, [], v => by simp [iadd, ipev]
  | a :: p, b :: q, v => by
      simp only [iadd, ipev, ipev_iadd p q v]; push_cast; ring

lemma ipev_ismul (a : ℤ) : ∀ (p : List ℤ) (v : ℝ), ipev (ismul a p) v = a * ipev p v
  | [], v => by simp [ismul, ipev]
  | b :: p, v => by
      have := ipev_ismul a p v
      simp only [ismul, List.map_cons, ipev] at this ⊢
      rw [this]; push_cast; ring

lemma ipev_imul : ∀ (p q : List ℤ) (v : ℝ), ipev (imul p q) v = ipev p v * ipev q v
  | [], q, v => by simp [imul, ipev]
  | a :: p, q, v => by
      rw [imul, ipev_iadd, ipev_ismul, ipev, ipev_imul p q v, ipev]; push_cast; ring

lemma ipev_neg : ∀ (p : List ℤ) (v : ℝ), ipev (p.map (fun a => -a)) v = - ipev p v
  | [], v => by simp [ipev]
  | a :: p, v => by
      simp only [List.map_cons, ipev, ipev_neg p v]; push_cast; ring

lemma abs_ipev_le (v : ℝ) (hv : |v| ≤ 1) : ∀ p : List ℤ, |ipev p v| ≤ inorm p
  | [] => by simp [ipev, inorm]
  | a :: p => by
      have ih := abs_ipev_le v hv p
      simp only [ipev, inorm]
      push_cast
      have h1 : |v * ipev p v| ≤ inorm p := by
        rw [abs_mul]
        calc |v| * |ipev p v| ≤ 1 * inorm p :=
              mul_le_mul hv ih (abs_nonneg _) zero_le_one
          _ = inorm p := one_mul _
      have h2 : |(a : ℝ)| = (a.natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      calc |(a : ℝ) + v * ipev p v| ≤ |(a : ℝ)| + |v * ipev p v| := abs_add_le _ _
        _ ≤ (a.natAbs : ℝ) + inorm p := by rw [h2]; linarith

lemma ipev_take_drop (v : ℝ) : ∀ (n : ℕ) (p : List ℤ),
    ipev p v = ipev (p.take n) v + v ^ n * ipev (p.drop n) v
  | 0, p => by simp [ipev]
  | n + 1, [] => by simp [ipev]
  | n + 1, a :: p => by
      simp only [List.take_succ_cons, List.drop_succ_cons, ipev]
      rw [ipev_take_drop v n p]; ring

/-- The fixed-point scale `2^50`. -/
def SC : ℕ := 1125899906842624

lemma SC_pos : (0 : ℝ) < SC := by norm_num [SC]

lemma ipev_round (v : ℝ) (hv : |v| ≤ 1) : ∀ p : List ℤ,
    |ipev p v - SC * ipev (p.map (fun a => a / (SC : ℤ))) v| ≤ SC * p.length
  | [] => by simp [ipev]
  | a :: p => by
      have ih := ipev_round v hv p
      simp only [List.map_cons, ipev, List.length_cons]
      have hSCz : (0 : ℤ) < (SC : ℤ) := by norm_num [SC]
      have hm0 := Int.emod_nonneg a (ne_of_gt hSCz)
      have hm1 := Int.emod_lt_of_pos a hSCz
      have hdm := Int.mul_ediv_add_emod a (SC : ℤ)
      have e : (a : ℝ) = (SC : ℝ) * ((a / (SC : ℤ) : ℤ) : ℝ) + ((a % (SC : ℤ) : ℤ) : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hdm
        push_cast at this; linarith
      have hm0' : (0 : ℝ) ≤ ((a % (SC : ℤ) : ℤ) : ℝ) := by exact_mod_cast hm0
      have hm1' : ((a % (SC : ℤ) : ℤ) : ℝ) < SC := by exact_mod_cast hm1
      have key : (a : ℝ) + v * ipev p v -
          SC * (((a / (SC : ℤ) : ℤ) : ℝ) + v * ipev (p.map (fun a => a / (SC : ℤ))) v) =
          ((a % (SC : ℤ) : ℤ) : ℝ) +
            v * (ipev p v - SC * ipev (p.map (fun a => a / (SC : ℤ))) v) := by
        rw [e]; ring
      rw [key]
      have h2 : |v * (ipev p v - SC * ipev (p.map (fun a => a / (SC : ℤ))) v)| ≤ SC * p.length := by
        rw [abs_mul]
        calc |v| * |ipev p v - SC * ipev (p.map (fun a => a / (SC : ℤ))) v|
            ≤ 1 * (SC * p.length) := mul_le_mul hv ih (abs_nonneg _) zero_le_one
          _ = SC * p.length := one_mul _
      have h3 := abs_add_le ((a % (SC : ℤ) : ℤ) : ℝ)
        (v * (ipev p v - SC * ipev (p.map (fun a => a / (SC : ℤ))) v))
      rw [abs_of_nonneg hm0'] at h3
      push_cast
      nlinarith

/-- A pointwise Taylor model: `|x·2^50 − p(v)| ≤ r`. -/
structure TM where
  p : List ℤ
  r : ℕ

def TM.Mem (A : TM) (v x : ℝ) : Prop := |x * SC - ipev A.p v| ≤ A.r

/-- Number of retained coefficients (degree `4`). -/
def DEG : ℕ := 5

def TM.add (A B : TM) : TM := ⟨iadd A.p B.p, A.r + B.r⟩
def TM.neg (A : TM) : TM := ⟨A.p.map (fun a => -a), A.r⟩
def TM.sub (A B : TM) : TM := A.add B.neg
def TM.mul (A B : TM) : TM :=
  let P := imul A.p B.p
  let lo := P.take DEG
  let err := A.r * (inorm B.p + B.r) + inorm A.p * B.r + inorm (P.drop DEG)
  ⟨lo.map (fun a => a / (SC : ℤ)), err / SC + 1 + lo.length⟩
def TM.ofQ (P : List ℚ) : TM := ⟨P.map (fun q : ℚ => ⌊q * (SC : ℚ)⌋), P.length⟩
def TM.const (q : ℚ) : TM := TM.ofQ [q]
def TM.widen (A : TM) (w : ℕ) : TM := ⟨A.p, A.r + w⟩
def TM.hornerQ : List ℚ → TM → TM
  | [], _ => ⟨[], 0⟩
  | c :: cs, X => (TM.const c).add (X.mul (TM.hornerQ cs X))
def TM.pos (A : TM) : Bool := decide ((((A.r + inorm A.p.tail : ℕ)) : ℤ) < A.p.headD 0)

section TMlemmas
variable {v : ℝ}

lemma TM.mem_add {A B : TM} {x y : ℝ} (hA : A.Mem v x) (hB : B.Mem v y) :
    (A.add B).Mem v (x + y) := by
  unfold TM.Mem TM.add at *
  simp only [ipev_iadd]
  push_cast
  have := abs_add_le (x * SC - ipev A.p v) (y * SC - ipev B.p v)
  calc |(x + y) * SC - (ipev A.p v + ipev B.p v)|
      = |(x * SC - ipev A.p v) + (y * SC - ipev B.p v)| := by ring_nf
    _ ≤ _ := this
    _ ≤ _ := add_le_add hA hB

lemma TM.mem_neg {A : TM} {x : ℝ} (hA : A.Mem v x) : A.neg.Mem v (-x) := by
  unfold TM.Mem TM.neg at *
  simp only [ipev_neg]
  rw [show -x * SC - -ipev A.p v = -(x * SC - ipev A.p v) by ring, abs_neg]
  exact hA

lemma TM.mem_sub {A B : TM} {x y : ℝ} (hA : A.Mem v x) (hB : B.Mem v y) :
    (A.sub B).Mem v (x - y) := by
  rw [sub_eq_add_neg]; exact TM.mem_add hA (TM.mem_neg hB)

lemma nat_div_bound (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  have h := Nat.div_add_mod n d
  have hm := Nat.mod_lt n hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hdR]
  have e : (n : ℝ) = d * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) := by
    exact_mod_cast h.symm
  have : ((n % d : ℕ) : ℝ) < d := by exact_mod_cast hm
  rw [e]; nlinarith

lemma TM.mem_mul {A B : TM} {x y : ℝ} (hv : |v| ≤ 1) (hA : A.Mem v x) (hB : B.Mem v y) :
    (A.mul B).Mem v (x * y) := by
  unfold TM.Mem at *
  simp only [TM.mul]
  set a := ipev A.p v
  set b := ipev B.p v
  set P := imul A.p B.p
  have hP : ipev P v = a * b := ipev_imul _ _ _
  have hsplit := ipev_take_drop v DEG P
  have hhi := abs_ipev_le v hv (P.drop DEG)
  have hround := ipev_round v hv (P.take DEG)
  have hna := abs_ipev_le v hv A.p
  have hnb := abs_ipev_le v hv B.p
  have hvD : |v ^ DEG| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hv
  have hSC := SC_pos
  -- bound on |X Y - a b|
  have hY : |y * SC| ≤ inorm B.p + B.r := by
    have := abs_sub_abs_le_abs_sub (y * SC) b
    linarith
  have hXY : |x * SC * (y * SC) - a * b| ≤ A.r * (inorm B.p + B.r) + inorm A.p * B.r := by
    have e : x * SC * (y * SC) - a * b = (x * SC - a) * (y * SC) + a * (y * SC - b) := by ring
    rw [e]
    calc |(x * SC - a) * (y * SC) + a * (y * SC - b)|
        ≤ |(x * SC - a) * (y * SC)| + |a * (y * SC - b)| := abs_add_le _ _
      _ = |x * SC - a| * |y * SC| + |a| * |y * SC - b| := by
          rw [abs_mul (x * SC - a) (y * SC), abs_mul a (y * SC - b)]
      _ ≤ A.r * (inorm B.p + B.r) + inorm A.p * B.r := by
          apply add_le_add
          · exact mul_le_mul hA hY (abs_nonneg _) (Nat.cast_nonneg _)
          · exact mul_le_mul hna hB (abs_nonneg _) (Nat.cast_nonneg _)
  have hhi' : |v ^ DEG * ipev (P.drop DEG) v| ≤ inorm (P.drop DEG) := by
    rw [abs_mul]
    calc |v ^ DEG| * |ipev (P.drop DEG) v| ≤ 1 * inorm (P.drop DEG) :=
          mul_le_mul hvD hhi (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  set lo' := (P.take DEG).map (fun a => a / (SC : ℤ))
  set err := A.r * (inorm B.p + B.r) + inorm A.p * B.r + inorm (P.drop DEG)
  have htot : |x * SC * (y * SC) - SC * ipev lo' v| ≤ err + SC * (P.take DEG).length := by
    have e : x * SC * (y * SC) - SC * ipev lo' v =
        (x * SC * (y * SC) - a * b) + v ^ DEG * ipev (P.drop DEG) v +
          (ipev (P.take DEG) v - SC * ipev lo' v) := by
      rw [← hP, hsplit]; ring
    rw [e]
    have := abs_add_le ((x * SC * (y * SC) - a * b) + v ^ DEG * ipev (P.drop DEG) v)
      (ipev (P.take DEG) v - SC * ipev lo' v)
    have := abs_add_le (x * SC * (y * SC) - a * b) (v ^ DEG * ipev (P.drop DEG) v)
    simp only [err]; push_cast
    linarith
  have hdiv := nat_div_bound err SC (by norm_num [SC])
  have e2 : x * y * SC - ipev lo' v = (x * SC * (y * SC) - SC * ipev lo' v) / SC := by
    field_simp
  rw [e2, abs_div, abs_of_pos hSC, div_le_iff₀ hSC]
  have : (err : ℝ) ≤ (((err / SC : ℕ) : ℝ) + 1) * SC := by
    rw [div_le_iff₀ hSC] at hdiv; linarith
  push_cast
  nlinarith

lemma TM.mem_ofQ (hv : |v| ≤ 1) : ∀ P : List ℚ, (TM.ofQ P).Mem v (peval P v)
  | [] => by simp [TM.ofQ, TM.Mem, peval, ipev]
  | c :: P => by
      have ih := TM.mem_ofQ hv P
      unfold TM.Mem TM.ofQ at *
      simp only [List.map_cons, peval, ipev, List.length_cons] at ih ⊢
      have hf1 : ((⌊c * (SC : ℚ)⌋ : ℤ) : ℝ) ≤ (c : ℝ) * SC := by
        have := Int.floor_le (c * (SC : ℚ))
        exact_mod_cast this
      have hf2 : (c : ℝ) * SC < ((⌊c * (SC : ℚ)⌋ : ℤ) : ℝ) + 1 := by
        have := Int.lt_floor_add_one (c * (SC : ℚ))
        exact_mod_cast this
      have e : ((c : ℝ) + v * peval P v) * SC - (((⌊c * (SC : ℚ)⌋ : ℤ) : ℝ) + v * ipev
          (P.map (fun q : ℚ => ⌊q * (SC : ℚ)⌋)) v) = ((c : ℝ) * SC - ((⌊c * (SC : ℚ)⌋ : ℤ) : ℝ)) +
          v * (peval P v * SC - ipev (P.map (fun q : ℚ => ⌊q * (SC : ℚ)⌋)) v) := by ring
      rw [e]
      have h2 : |v * (peval P v * SC - ipev (P.map (fun q : ℚ => ⌊q * (SC : ℚ)⌋)) v)| ≤ P.length := by
        rw [abs_mul]
        calc |v| * |peval P v * SC - ipev (P.map (fun q : ℚ => ⌊q * (SC : ℚ)⌋)) v| ≤ 1 * P.length :=
              mul_le_mul hv ih (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      have h3 := abs_add_le ((c : ℝ) * SC - ((⌊c * (SC : ℚ)⌋ : ℤ) : ℝ))
        (v * (peval P v * SC - ipev (P.map (fun q : ℚ => ⌊q * (SC : ℚ)⌋)) v))
      have hc0 : |(c : ℝ) * SC - ((⌊c * (SC : ℚ)⌋ : ℤ) : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      push_cast
      linarith

lemma TM.mem_const (hv : |v| ≤ 1) (q : ℚ) : (TM.const q).Mem v q := by
  have := TM.mem_ofQ hv [q]
  simp only [peval, mul_zero, add_zero] at this
  exact this

lemma TM.mem_widen {A : TM} {x y : ℝ} (w : ℕ) (hA : A.Mem v x) (h : |y - x| * SC ≤ w) :
    (A.widen w).Mem v y := by
  unfold TM.Mem TM.widen at *
  push_cast
  have e : y * SC - ipev A.p v = (y - x) * SC + (x * SC - ipev A.p v) := by ring
  rw [e]
  have h1 := abs_add_le ((y - x) * SC) (x * SC - ipev A.p v)
  rw [abs_mul, abs_of_pos SC_pos] at h1
  linarith

lemma TM.mem_hornerQ (hv : |v| ≤ 1) {X : TM} {x : ℝ} (hX : X.Mem v x) :
    ∀ cs : List ℚ, (TM.hornerQ cs X).Mem v (peval cs x)
  | [] => by simp [TM.hornerQ, TM.Mem, peval, ipev]
  | c :: cs => by
      simp only [TM.hornerQ, peval]
      exact TM.mem_add (TM.mem_const hv c) (TM.mem_mul hv hX (TM.mem_hornerQ hv hX cs))

lemma TM.pos_sound {A : TM} {x : ℝ} (hv : |v| ≤ 1) (hA : A.Mem v x) (h : A.pos = true) :
    0 < x := by
  unfold TM.pos at h
  unfold TM.Mem at hA
  rw [decide_eq_true_eq] at h
  rcases hp : A.p with _ | ⟨a, q⟩
  · rw [hp] at h; simp [inorm] at h <;> omega
  · rw [hp] at h hA
    simp only [List.tail_cons, List.headD_cons] at h
    simp only [ipev] at hA
    have hq := abs_ipev_le v hv q
    have hvq : |v * ipev q v| ≤ inorm q := by
      rw [abs_mul]
      calc |v| * |ipev q v| ≤ 1 * inorm q := mul_le_mul hv hq (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have h' : ((A.r : ℝ) + inorm q) < a := by exact_mod_cast h
    have h1 := (abs_le.mp hA).1
    have h2 := (abs_le.mp hvq).1
    have : 0 < x * SC := by linarith
    exact pos_of_mul_pos_left this SC_pos.le

lemma TM.mem_exact {p : List ℤ} {x : ℝ} (h : x * SC = ipev p v) : (TM.mk p 0).Mem v x := by
  unfold TM.Mem; rw [h]; simp

end TMlemmas

/-! ## Part 4. Taylor bounds for `sin` -/

lemma sin_taylor (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 2) (N : ℕ) :
    |Real.sin t - ∑ i ∈ Finset.range N, (-1) ^ i * (t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))|
      ≤ t ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) := by
  set f : ℕ → ℝ := fun i => t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) with hf
  have hsum : Summable f := by
    have := (Real.summable_pow_div_factorial t).comp_injective
      (i := fun i : ℕ => 2 * i + 1) (fun a b h => by simp at h; omega)
    exact this
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [hf]
    have e1 : (2 * (i + 1) + 1) = (2 * i + 1) + 2 := by ring
    rw [e1, Nat.factorial_succ, Nat.factorial_succ, pow_add]
    have hfac : (0 : ℝ) < ((2 * i + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hp : (0 : ℝ) ≤ t ^ (2 * i + 1) := pow_nonneg h0 _
    push_cast
    rw [div_le_div_iff₀ (by positivity) hfac]
    have ht2 : t ^ 2 ≤ ((2 * i + 1 : ℝ) + 1 + 1) * ((2 * i + 1 : ℝ) + 1) := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      nlinarith
    have := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hp hfac.le)
    nlinarith
  have hb := alternating_series_error_bound f hanti hsum N
  have hs : ∑' i, (-1) ^ i * f i = Real.sin t := by
    rw [Real.sin_eq_tsum]
    congr 1; ext i; simp only [hf]; ring
  rw [hs] at hb
  exact hb

/-- Coefficients of `sinc(t) ≈ Σ_{i<8} (−1)^i t^{2i}/(2i+1)!` as a polynomial in `t²`. -/
def sincQ : List ℚ := [1, -1/6, 1/120, -1/5040, 1/362880, -1/39916800, 1/6227020800,
  -1/1307674368000]

/-- Coefficients of `(t − sin t)/t³ ≈ Σ_{1≤i<8} (−1)^{i+1} t^{2i−2}/(2i+1)!` in `t²`. -/
def tsrQ : List ℚ := [1/6, -1/120, 1/5040, -1/362880, 1/39916800, -1/6227020800,
  1/1307674368000]

lemma sinc_bound (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 2) :
    |Real.sin t / t - peval sincQ (t * t)| ≤ t ^ 16 / 355687428096000 ∧
    |(t - Real.sin t) / t ^ 3 - peval tsrQ (t * t)| ≤ t ^ 14 / 355687428096000 := by
  have h := sin_taylor t h0.le h1 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have hE : |Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
      t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000)|
      ≤ t ^ 17 / 355687428096000 := by
    convert h using 2
    · norm_num [Nat.factorial]; ring
    · norm_num [Nat.factorial]
  have ht : t ≠ 0 := ne_of_gt h0
  constructor
  · have e : Real.sin t / t - peval sincQ (t * t) =
        (Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
          t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000)) / t := by
      simp only [sincQ, peval]; push_cast; field_simp; ring
    rw [e, abs_div, abs_of_pos h0, div_le_iff₀ h0]
    calc _ ≤ t ^ 17 / 355687428096000 := hE
      _ = t ^ 16 / 355687428096000 * t := by ring
  · have e : (t - Real.sin t) / t ^ 3 - peval tsrQ (t * t) =
        -(Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
          t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000)) / t ^ 3 := by
      simp only [tsrQ, peval]; push_cast; field_simp; ring
    have h3 : 0 < t ^ 3 := by positivity
    rw [e, abs_div, abs_neg, abs_of_pos h3, div_le_iff₀ h3]
    calc _ ≤ t ^ 17 / 355687428096000 := hE
      _ = t ^ 14 / 355687428096000 * t ^ 3 := by ring

/-! ## Part 5. Inputs of the Taylor-model computation -/

def piTM : TM := ⟨[3537118876014220], 1⟩

lemma piTM_mem (v : ℝ) : piTM.Mem v Real.pi := by
  unfold TM.Mem piTM
  simp only [ipev, mul_zero, add_zero]
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [abs_le]
  norm_num [SC]
  constructor <;> nlinarith

/-- The exact linear model of `(a + b v)/128`. -/
def linTM (a b : ℤ) : TM := ⟨[a * 8796093022208, b * 8796093022208], 0⟩

lemma linTM_mem (v : ℝ) (a b : ℤ) : (linTM a b).Mem v ((a + b * v) / 128) := by
  apply TM.mem_exact
  simp only [ipev, SC]
  push_cast
  ring

/-- The spline with coefficients `c` on the knot interval `k`, in the variable `v ∈ [−1, 1]`
(`s = (1 + v)/2`). -/
def splineTM (c : Fin 35 → ℚ) (k : ℕ) : TM := TM.ofQ (pcompLin (1 / 2) (1 / 2) (splineQ c k))

lemma bern11_zero (i : Fin 12) : DelaunayStretch.bernstein 11 i 0 = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [DelaunayStretch.bernstein]

lemma bern11_one (j : Fin 12) : DelaunayStretch.bernstein 11 j 1 = if j = 11 then 1 else 0 := by
  fin_cases j <;> simp [DelaunayStretch.bernstein]

lemma familyV_00 (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ : ℝ) :
    familyV V γ 0 0 = familySpline (V 0 0) γ := by
  unfold familyV familySpline
  simp only [bern11_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq']

lemma familyV_01 (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ : ℝ) :
    familyV V γ 0 1 = familySpline (V 0 11) γ := by
  unfold familyV familySpline
  simp only [bern11_zero, bern11_one, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-- Common setting: `γ ∈ [0, π/2)` lies in the knot interval `k`, at the local
coordinate `v`, and all four splines are explicit polynomials in `v`. -/
lemma setup (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < Real.pi / 2) :
    ∃ k : ℕ, k ≤ 31 ∧ ∃ v : ℝ, |v| ≤ 1 ∧ γ = Real.pi * ((2 * k + 1 : ℝ) + v) / 128 ∧
      ∀ c : Fin 35 → ℚ, familySpline c γ = peval (pcompLin (1 / 2) (1 / 2) (splineQ c k)) v := by
  have hπ := Real.pi_pos
  set τ := 2 * γ / Real.pi with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hτ1 : τ < 1 := by
    rw [hτ, div_lt_one hπ]; linarith
  obtain ⟨k, hk, hk0, hk1⟩ := exists_interval τ hτ0 hτ1.le
  have hk1' : τ < ((k : ℝ) + 1) / 32 := by
    rcases hk1 with h | ⟨_, h⟩
    · exact h
    · linarith
  refine ⟨k, hk, 2 * (32 * τ - k) - 1, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [hτ]; field_simp; ring
  · intro c
    rw [familySpline, spline_local c k hk τ hk0 hk1, peval_pcompLin]
    congr 1; push_cast; ring

lemma t_mem (k : ℕ) (v : ℝ) (hv : |v| ≤ 1) (γ : ℝ)
    (hγ : γ = Real.pi * ((2 * k + 1 : ℝ) + v) / 128) :
    (piTM.mul (linTM (63 - 2 * (k : ℤ)) (-1))).Mem v (Real.pi / 2 - γ) := by
  have := TM.mem_mul hv (piTM_mem v) (linTM_mem v (63 - 2 * (k : ℤ)) (-1))
  convert this using 1
  rw [hγ]; push_cast; ring

lemma g_mem (k : ℕ) (v : ℝ) (hv : |v| ≤ 1) (γ : ℝ)
    (hγ : γ = Real.pi * ((2 * k + 1 : ℝ) + v) / 128) :
    (piTM.mul (linTM (2 * (k : ℤ) + 1) 1)).Mem v γ := by
  have := TM.mem_mul hv (piTM_mem v) (linTM_mem v (2 * (k : ℤ) + 1) 1)
  convert this using 1
  rw [hγ]; push_cast; ring

lemma trig_setup (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < Real.pi / 2) :
    0 < Real.pi / 2 - γ ∧ Real.cos γ = (Real.pi / 2 - γ) * (Real.sin (Real.pi / 2 - γ) / (Real.pi / 2 - γ)) ∧
    0 < Real.sin (Real.pi / 2 - γ) / (Real.pi / 2 - γ) ∧
    |Real.sin (Real.pi / 2 - γ) / (Real.pi / 2 - γ) - peval sincQ ((Real.pi / 2 - γ) * (Real.pi / 2 - γ))| * (SC : ℝ) ≤ 6000 ∧
    |(Real.pi / 2 - γ - Real.sin (Real.pi / 2 - γ)) / (Real.pi / 2 - γ) ^ 3 -
      peval tsrQ ((Real.pi / 2 - γ) * (Real.pi / 2 - γ))| * (SC : ℝ) ≤ 2300 := by
  set t := Real.pi / 2 - γ with ht
  have ht0 : 0 < t := by linarith
  have hp := Real.pi_lt_d2
  have ht1 : t ≤ 8 / 5 := by linarith
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  obtain ⟨hb1, hb2⟩ := sinc_bound t ht0 (by linarith)
  refine ⟨ht0, ?_, div_pos hsin ht0, ?_, ?_⟩
  · have e : t * (Real.sin t / t) = Real.sin t := by field_simp
    rw [e, ht, Real.sin_pi_div_two_sub]
  · have h16 : t ^ 16 ≤ (8 / 5) ^ 16 := pow_le_pow_left₀ ht0.le ht1 16
    have := mul_le_mul_of_nonneg_right hb1 SC_pos.le
    refine this.trans ?_
    norm_num [SC] at h16 ⊢
    nlinarith
  · have h14 : t ^ 14 ≤ (8 / 5) ^ 14 := pow_le_pow_left₀ ht0.le ht1 14
    have := mul_le_mul_of_nonneg_right hb2 SC_pos.le
    refine this.trans ?_
    norm_num [SC] at h14 ⊢
    nlinarith
/-! ## Part 6. The checks (b) -/

/-- Positivity of the upper and lower divided slacks for one middle term `M`. -/
def okB (tTT S2 lo0 c2 GT M : TM) : Bool :=
  (tTT.add (S2.mul (GT.sub M))).pos && (lo0.sub (c2.mul (GT.sub M))).pos

def chkB1 (tT gT GT BT DT : TM) (s : ℚ) : Bool :=
  let t2 := tT.mul tT
  let S := (TM.hornerQ sincQ t2).widen 6000
  let T := (TM.hornerQ tsrQ t2).widen 2300
  let c := tT.mul S
  let Bp := BT.add (TM.const s)
  okB (tT.mul T) (S.mul S) (((tT.add gT).add gT).sub c) (c.mul c) GT Bp &&
  okB (tT.mul T) (S.mul S) (((tT.add gT).add gT).sub c) (c.mul c) GT
    (((TM.const (-1 / 2)).mul Bp).add ((TM.const (3 / 2)).mul DT)) &&
  okB (tT.mul T) (S.mul S) (((tT.add gT).add gT).sub c) (c.mul c) GT
    (((TM.const (-2)).mul Bp).sub ((TM.const 2).mul DT))

lemma okB_sound {v : ℝ} (hv : |v| ≤ 1) {tTT S2 lo0 c2 GT M : TM} {a b l q G m : ℝ}
    (h1 : tTT.Mem v a) (h2 : S2.Mem v b) (h3 : lo0.Mem v l) (h4 : c2.Mem v q) (h5 : GT.Mem v G)
    (h6 : M.Mem v m) (h : okB tTT S2 lo0 c2 GT M = true) :
    0 < a + b * (G - m) ∧ 0 < l - q * (G - m) := by
  unfold okB at h
  rw [Bool.and_eq_true] at h
  exact ⟨TM.pos_sound hv (TM.mem_add h1 (TM.mem_mul hv h2 (TM.mem_sub h5 h6))) h.1,
    TM.pos_sound hv (TM.mem_sub h3 (TM.mem_mul hv h4 (TM.mem_sub h5 h6))) h.2⟩

lemma chkB1_sound {v : ℝ} (hv : |v| ≤ 1) {tT gT GT BT DT : TM} {t g S T G B D : ℝ} (s : ℚ)
    (ht : tT.Mem v t) (hg : gT.Mem v g) (hS : |S - peval sincQ (t * t)| * (SC : ℝ) ≤ 6000)
    (hT : |T - peval tsrQ (t * t)| * (SC : ℝ) ≤ 2300)
    (hG : GT.Mem v G) (hB : BT.Mem v B) (hD : DT.Mem v D) (h : chkB1 tT gT GT BT DT s = true) :
    ∀ m : ℝ, (m = B + s ∨ m = ((-1 / 2 : ℚ) : ℝ) * (B + s) + ((3 / 2 : ℚ) : ℝ) * D ∨
      m = ((-2 : ℚ) : ℝ) * (B + s) - ((2 : ℚ) : ℝ) * D) →
      0 < t * T + S * S * (G - m) ∧ 0 < ((t + g) + g) - t * S - (t * S) * (t * S) * (G - m) := by
  have hS' := TM.mem_widen 6000 (TM.mem_hornerQ hv (TM.mem_mul hv ht ht) sincQ) hS
  have hT' := TM.mem_widen 2300 (TM.mem_hornerQ hv (TM.mem_mul hv ht ht) tsrQ) hT
  have h1 := TM.mem_mul hv ht hT'
  have h2 := TM.mem_mul hv hS' hS'
  have hc := TM.mem_mul hv ht hS'
  have h3 := TM.mem_sub (TM.mem_add (TM.mem_add ht hg) hg) hc
  have h4 := TM.mem_mul hv hc hc
  have hBp := TM.mem_add hB (TM.mem_const hv s)
  unfold chkB1 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨ha, hb⟩, hc'⟩ := h
  intro m hm
  rcases hm with rfl | rfl | rfl
  · exact okB_sound hv h1 h2 h3 h4 hG hBp ha
  · exact okB_sound hv h1 h2 h3 h4 hG (TM.mem_add (TM.mem_mul hv (TM.mem_const hv _) hBp)
      (TM.mem_mul hv (TM.mem_const hv _) hD)) hb
  · exact okB_sound hv h1 h2 h3 h4 hG (TM.mem_sub (TM.mem_mul hv (TM.mem_const hv _) hBp)
      (TM.mem_mul hv (TM.mem_const hv _) hD)) hc'

def chkB (k : ℕ) : Bool :=
  chkB1 (piTM.mul (linTM (63 - 2 * (k : ℤ)) (-1))) (piTM.mul (linTM (2 * (k : ℤ) + 1) 1))
    (splineTM (hstarV 0 11) k) (splineTM hstarB k) (splineTM hstarD k) (1 / 50) &&
  chkB1 (piTM.mul (linTM (63 - 2 * (k : ℤ)) (-1))) (piTM.mul (linTM (2 * (k : ℤ) + 1) 1))
    (splineTM (hstarV 0 11) k) (splineTM hstarB k) (splineTM hstarD k) (-(1 / 50))

theorem chkB_all : ∀ k < 32, chkB k = true := by
  decide +kernel

lemma alg_b (L c t g S T G M e : ℝ) (hL : L = t + g) (hc : c = t * S)
    (hT : t * S = t - t ^ 3 * T) (ht : 0 < t) (he : e = (g - c ^ 2 * G) + c ^ 2 * M)
    (hup : 0 < t * T + S * S * (G - M))
    (hlo : 0 < ((t + g) + g) - t * S - (t * S) * (t * S) * (G - M)) :
    |e| ≤ L - c := by
  subst hL hc he
  rw [abs_le]
  constructor
  · nlinarith
  · have e1 : t + g - t * S - (g - (t * S) ^ 2 * G + (t * S) ^ 2 * M) =
        t ^ 2 * (t * T + S * S * (G - M)) := by
      linear_combination (-1 : ℝ) * hT
    have : 0 ≤ t ^ 2 * (t * T + S * S * (G - M)) := by positivity
    linarith

end CheckBD

open CheckBD in
theorem solution :
    ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 → ∀ s : ℝ, (s = 1 / 50 ∨ s = -(1 / 50)) →
      |(γ - Real.cos γ ^ 2 * familyV hstarV γ 0 1) + Real.cos γ ^ 2 * (familySpline hstarB γ + s)| ≤
          Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV hstarV γ 0 1) - Real.cos γ ^ 2 * (familySpline hstarB γ + s) / 2 +
          3 / 2 * (Real.cos γ ^ 2 * familySpline hstarD γ)| ≤ Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV hstarV γ 0 1) - 2 * (Real.cos γ ^ 2 * (familySpline hstarB γ + s)) -
          2 * (Real.cos γ ^ 2 * familySpline hstarD γ)| ≤ Real.pi / 2 - Real.cos γ := by
  intro γ hγ0 hγ1 s hs
  obtain ⟨k, hk, v, hv, hγv, hspl⟩ := setup γ hγ0 hγ1
  obtain ⟨ht0, hc, hS0, hSb, hTb⟩ := trig_setup γ hγ0 hγ1
  rw [familyV_01, hspl, hspl, hspl]
  set t := Real.pi / 2 - γ with ht_def
  set S := Real.sin t / t with hS_def
  set T := (t - Real.sin t) / t ^ 3 with hT_def
  have hTS : t * S = t - t ^ 3 * T := by
    rw [hS_def, hT_def]; field_simp; ring
  have hL : Real.pi / 2 = t + γ := by rw [ht_def]; ring
  set G := peval (pcompLin (1 / 2) (1 / 2) (splineQ (hstarV 0 11) k)) v
  set B := peval (pcompLin (1 / 2) (1 / 2) (splineQ hstarB k)) v
  set D := peval (pcompLin (1 / 2) (1 / 2) (splineQ hstarD k)) v
  have hchk := chkB_all k (by omega)
  unfold chkB at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨q, hqs, hq⟩ : ∃ q : ℚ, (q : ℝ) = s ∧ chkB1 (piTM.mul (linTM (63 - 2 * (k : ℤ)) (-1)))
      (piTM.mul (linTM (2 * (k : ℤ) + 1) 1)) (splineTM (hstarV 0 11) k) (splineTM hstarB k)
      (splineTM hstarD k) q = true := by
    rcases hs with rfl | rfl
    · exact ⟨1 / 50, by norm_num, hchk.1⟩
    · exact ⟨-(1 / 50), by norm_num, hchk.2⟩
  have hm := chkB1_sound hv q (t_mem k v hv γ hγv) (g_mem k v hv γ hγv) hSb hTb
    (TM.mem_ofQ hv (pcompLin (1 / 2) (1 / 2) (splineQ (hstarV 0 11) k)))
    (TM.mem_ofQ hv (pcompLin (1 / 2) (1 / 2) (splineQ hstarB k)))
    (TM.mem_ofQ hv (pcompLin (1 / 2) (1 / 2) (splineQ hstarD k))) hq
  obtain ⟨u1, l1⟩ := hm _ (Or.inl rfl)
  obtain ⟨u2, l2⟩ := hm _ (Or.inr (Or.inl rfl))
  obtain ⟨u3, l3⟩ := hm _ (Or.inr (Or.inr rfl))
  rw [← hqs]
  refine ⟨alg_b _ _ _ _ _ _ _ _ _ hL hc hTS ht0 ?_ u1 l1,
    alg_b _ _ _ _ _ _ _ _ _ hL hc hTS ht0 ?_ u2 l2,
    alg_b _ _ _ _ _ _ _ _ _ hL hc hTS ht0 ?_ u3 l3⟩ <;> push_cast <;> ring
