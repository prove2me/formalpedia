-- Prove2me | solution 1 for CookSensitivity.ChvatalRank.exists_flat_direction_of_no_integer_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T11:53:22.414622+00:00
-- url     : https://prove2.me/submissions/431bcc1c-9bf4-449d-b3fd-38fcdd8bb60c

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

set_option autoImplicit false

namespace FlatFd3

open Matrix

/-- Scaling a nonzero rational vector to a nonzero integral vector (clearing denominators). -/
lemma exists_int_scale {n : ℕ} (a : Fin n → ℚ) (ha : a ≠ 0) :
    ∃ (w : Fin n → ℤ) (N : ℚ), 0 < N ∧ w ≠ 0 ∧ ∀ j, (w j : ℚ) = N * a j := by
  classical
  set M : ℕ := ∏ l, (a l).den with hM
  have hMpos : 0 < M := Finset.prod_pos (fun l _ => (a l).pos)
  have hdvd : ∀ j, (a j).den ∣ M := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  refine ⟨fun j => (a j).num * ((M / (a j).den : ℕ) : ℤ), (M : ℚ), by exact_mod_cast hMpos, ?_, ?_⟩
  · intro hw
    apply ha
    funext j
    have h1 := congrFun hw j
    simp only [Pi.zero_apply, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · simpa using (Rat.num_eq_zero.mp h1)
    · exfalso
      have h2 : (M / (a j).den : ℕ) ≠ 0 := by
        have := Nat.div_pos (Nat.le_of_dvd hMpos (hdvd j)) (a j).pos
        omega
      exact h2 (by exact_mod_cast h1)
  · intro j
    have hd : ((M / (a j).den : ℕ) : ℚ) = (M : ℚ) / (a j).den := by
      rw [Nat.cast_div (hdvd j) (by exact_mod_cast (a j).den_nz)]
    show (((a j).num * ((M / (a j).den : ℕ) : ℤ) : ℤ) : ℚ) = (M : ℚ) * a j
    rw [Int.cast_mul, Int.cast_natCast, hd]
    have hden : ((a j).den : ℚ) ≠ 0 := by exact_mod_cast (a j).den_nz
    conv_rhs => rw [← Rat.num_div_den (a j)]
    field_simp

/-- Child A (degenerate case): a nonempty polyhedron `Dx ≤ d` with no point strictly satisfying
all its nonzero rows lies in a rational hyperplane, so it has width `0` in some integral
direction. -/
lemma flat_of_no_interior {n : ℕ} {ι : Type*} [Fintype ι] (D : Matrix ι (Fin n) ℚ) (d : ι → ℚ)
    (hne : ∃ x, D *ᵥ x ≤ d)
    (hint : ¬ ∃ c : Fin n → ℚ, ∀ i, D i ≠ 0 → (D *ᵥ c) i < d i) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ x, D *ᵥ x ≤ d → ∀ x', D *ᵥ x' ≤ d →
      (fun i => (w i : ℚ)) ⬝ᵥ (x - x') = 0 := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  -- some nonzero row is tight on the whole polyhedron
  have htight : ∃ i, D i ≠ 0 ∧ ∀ x, D *ᵥ x ≤ d → (D *ᵥ x) i = d i := by
    by_contra hcon
    push Not at hcon
    -- witnesses of strictness
    have hw : ∀ i, ∃ y, D *ᵥ y ≤ d ∧ (D i ≠ 0 → (D *ᵥ y) i < d i) := by
      intro i
      by_cases hi : D i = 0
      · exact ⟨x0, hx0, fun h => absurd hi h⟩
      · obtain ⟨y, hy, hyi⟩ := hcon i hi
        exact ⟨y, hy, fun _ => lt_of_le_of_ne (hy i) hyi⟩
    choose y hy hys using hw
    apply hint
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hk | hk
    · have := Fintype.card_eq_zero_iff.mp hk
      exact ⟨0, fun i => (IsEmpty.false i).elim⟩
    refine ⟨(1 / (Fintype.card ι : ℚ)) • ∑ i, y i, ?_⟩
    intro j hj
    have hlin : (D *ᵥ ((1 / (Fintype.card ι : ℚ)) • ∑ i, y i)) j = (1 / (Fintype.card ι : ℚ)) * ∑ i, (D *ᵥ y i) j := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
      simp [Finset.sum_apply]
    rw [hlin]
    have hkpos : (0 : ℚ) < Fintype.card ι := by exact_mod_cast hk
    have hsum : ∑ i, (D *ᵥ y i) j < ∑ _i : ι, d j := by
      apply Finset.sum_lt_sum
      · intro i _; exact hy i j
      · exact ⟨j, Finset.mem_univ _, hys j hj⟩
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hkpos]
    linarith
  obtain ⟨i, hi, hti⟩ := htight
  obtain ⟨w, N, -, hw0, hwj⟩ := exists_int_scale (D i) hi
  refine ⟨w, hw0, fun x hx x' hx' => ?_⟩
  have hdot : (fun j => (w j : ℚ)) ⬝ᵥ (x - x') = N * ((D *ᵥ x) i - (D *ᵥ x') i) := by
    have e : (fun j => (w j : ℚ)) = N • D i := by funext j; simp [hwj j]
    rw [e, smul_dotProduct, dotProduct_sub]
    simp [Matrix.mulVec, smul_eq_mul]
  rw [hdot, hti x hx, hti x' hx', sub_self, mul_zero]

/-- A strictly feasible point has a small box around it inside the polyhedron. -/
lemma exists_box {n k : ℕ} (D : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ) (c : Fin n → ℚ)
    (hc : ∀ i, D i ≠ 0 → (D *ᵥ c) i < d i) (hc0 : ∀ i, D i = 0 → 0 ≤ d i) :
    ∃ ρ : ℚ, 0 < ρ ∧ ∀ y : Fin n → ℚ, (∀ j, |y j - c j| ≤ ρ) → D *ᵥ y ≤ d := by
  classical
  set t : Fin k → ℚ := fun i => if D i ≠ 0 then d i - (D *ᵥ c) i else 1 with ht
  have htpos : ∀ i, 0 < t i := by
    intro i; simp only [ht]; split_ifs with h
    · linarith [hc i h]
    · exact one_pos
  set S : ℚ := 1 + ∑ i, ∑ j, |D i j| with hS
  have hSnn : 0 ≤ ∑ i, ∑ j, |D i j| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hSpos : 0 < S := by linarith
  set T : ℚ := ∑ i, 1 / t i with hT
  have hTi : ∀ i, 1 / t i ≤ T := fun i =>
    Finset.single_le_sum (f := fun i => 1 / t i) (fun i _ => le_of_lt (one_div_pos.mpr (htpos i)))
      (Finset.mem_univ i)
  have hTnn : 0 ≤ T := Finset.sum_nonneg (fun i _ => le_of_lt (one_div_pos.mpr (htpos i)))
  refine ⟨1 / (S * (1 + T)), by positivity, ?_⟩
  intro y hy i
  have hsplit : (D *ᵥ y) i = (D *ᵥ c) i + ∑ j, D i j * (y j - c j) := by
    rw [show (D *ᵥ y) i = ∑ j, D i j * y j from rfl, show (D *ᵥ c) i = ∑ j, D i j * c j from rfl,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  by_cases hi : D i = 0
  · have : (D *ᵥ y) i = 0 := by
      rw [show (D *ᵥ y) i = ∑ j, D i j * y j from rfl]
      simp [show ∀ j, D i j = 0 from fun j => congrFun hi j]
    rw [this]; exact hc0 i hi
  · have hrow : ∑ j, D i j * (y j - c j) ≤ (∑ j, |D i j|) * (1 / (S * (1 + T))) := by
      calc ∑ j, D i j * (y j - c j) ≤ ∑ j, |D i j * (y j - c j)| :=
            Finset.sum_le_sum (fun j _ => le_abs_self _)
        _ ≤ ∑ j, |D i j| * (1 / (S * (1 + T))) := by
            apply Finset.sum_le_sum; intro j _
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)
        _ = (∑ j, |D i j|) * (1 / (S * (1 + T))) := by rw [Finset.sum_mul]
    have hSi : ∑ j, |D i j| ≤ S := by
      have := Finset.single_le_sum (f := fun i => ∑ j, |D i j|)
        (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i)
      linarith [hS]
    have hti : t i = d i - (D *ᵥ c) i := by simp [ht, hi]
    have h1 : (∑ j, |D i j|) * (1 / (S * (1 + T))) ≤ S * (1 / (S * (1 + T))) :=
      mul_le_mul_of_nonneg_right hSi (by positivity)
    have h2 : S * (1 / (S * (1 + T))) = 1 / (1 + T) := by field_simp
    have h3 : 1 / (1 + T) ≤ t i := by
      have := hTi i
      rw [div_le_iff₀ (by linarith)]
      have hp := htpos i
      rw [div_le_iff₀ hp] at this
      nlinarith
    rw [hsplit]; linarith

/-- The bounded case (Lenstra's flatness theorem for polytopes), stated as a proposition so the
parent can be assembled from it. -/
def CoreBox : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (k : ℕ) (D : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ) (R : ℚ),
    (∀ x, D *ᵥ x ≤ d → (∀ j, |x j| ≤ R) → ¬ CookSensitivity.ChvatalRank.IsIntegral x) →
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ x, D *ᵥ x ≤ d → (∀ j, |x j| ≤ R) →
      ∀ x', D *ᵥ x' ≤ d → (∀ j, |x' j| ≤ R) →
      |((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ)| ≤
        ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)

/-- Assembly: the parent statement follows from the bounded case `CoreBox` (truncate by boxes,
the integral directions found are bounded via an interior box, pigeonhole over the radii). -/
theorem parent_of_core (hcore : CoreBox) {n : ℕ} (hn : 1 ≤ n) (P : Set (Fin n → ℚ))
    (hP : CookSensitivity.ChvatalRank.IsPolyhedron P)
    (hPZ : ∀ x ∈ P, ¬ CookSensitivity.ChvatalRank.IsIntegral x) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ x ∈ P, ∀ x' ∈ P,
      |((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ)| ≤
        ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) := by
  classical
  set B : ℝ := ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) with hB
  have hBnn : 0 ≤ B := by positivity
  obtain ⟨k, D, d, rfl⟩ := hP
  by_cases hne : ∃ x, D *ᵥ x ≤ d
  swap
  · refine ⟨Pi.single ⟨0, hn⟩ 1, ?_, ?_⟩
    · intro h; have := congrFun h ⟨0, hn⟩; simp at this
    · intro x hx; exact absurd ⟨x, hx⟩ hne
  by_cases hint : ∃ c : Fin n → ℚ, ∀ i, D i ≠ 0 → (D *ᵥ c) i < d i
  swap
  · obtain ⟨w, hw0, hw⟩ := flat_of_no_interior D d hne hint
    refine ⟨w, hw0, fun x hx x' hx' => ?_⟩
    rw [hw x hx x' hx']; simpa using hBnn
  obtain ⟨c, hc⟩ := hint
  obtain ⟨x0, hx0⟩ := hne
  have hc0 : ∀ i, D i = 0 → 0 ≤ d i := by
    intro i hi
    have h1 := hx0 i
    have e : (D *ᵥ x0) i = 0 := by
      rw [show (D *ᵥ x0) i = ∑ j, D i j * x0 j from rfl]
      simp [show ∀ j, D i j = 0 from fun j => congrFun hi j]
    linarith
  obtain ⟨ρ, hρ, hbox⟩ := exists_box D d c hc hc0
  set R0 : ℚ := ∑ j, |c j| + ρ with hR0
  have hcore' : ∀ m : ℕ, ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ x, D *ᵥ x ≤ d →
      (∀ j, |x j| ≤ max (m : ℚ) R0) → ∀ x', D *ᵥ x' ≤ d → (∀ j, |x' j| ≤ max (m : ℚ) R0) →
      |((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ)| ≤ B :=
    fun m => hcore n hn k D d (max (m : ℚ) R0) (fun x hx _ => hPZ x hx)
  choose g hg0 hg using hcore'
  -- the two test points `c ± ρ e_j`
  have hpt : ∀ (m : ℕ) (j : Fin n) (s : ℚ), |s| ≤ 1 →
      D *ᵥ (c + Pi.single j (s * ρ) : Fin n → ℚ) ≤ d ∧ ∀ l, |(c + Pi.single j (s * ρ) : Fin n → ℚ) l| ≤ max (m : ℚ) R0 := by
    intro m j s hs
    have hsl : ∀ l, |(Pi.single j (s * ρ) : Fin n → ℚ) l| ≤ ρ := by
      intro l
      by_cases hl : l = j
      · subst hl; simp only [Pi.single_eq_same, abs_mul, abs_of_pos hρ]
        nlinarith [abs_nonneg s]
      · simp [Pi.single_apply, hl, hρ.le]
    refine ⟨hbox _ (fun l => by simpa using hsl l), fun l => ?_⟩
    refine le_trans ?_ (le_max_right _ _)
    have h1 : |c l| ≤ ∑ j, |c j| :=
      Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg _) (Finset.mem_univ l)
    calc |(c + Pi.single j (s * ρ) : Fin n → ℚ) l| ≤ |c l| + |(Pi.single j (s * ρ) : Fin n → ℚ) l| := by
          simpa using abs_add_le (c l) ((Pi.single j (s * ρ) : Fin n → ℚ) l)
      _ ≤ R0 := by rw [hR0]; linarith [hsl l]
  have hcoef : ∀ m j, |(g m j : ℝ)| * (2 * (ρ : ℝ)) ≤ B := by
    intro m j
    obtain ⟨h1, h1'⟩ := hpt m j 1 (by norm_num)
    obtain ⟨h2, h2'⟩ := hpt m j (-1) (by norm_num)
    have := hg m _ h1 h1' _ h2 h2'
    have e : ((c + Pi.single j (1 * ρ) : Fin n → ℚ) - (c + Pi.single j (-1 * ρ))) =
        (Pi.single j (2 * ρ) : Fin n → ℚ) := by
      funext l; by_cases hl : l = j
      · subst hl; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]; ring
      · simp [Pi.single_apply, hl]
    rw [e, dotProduct_single] at this
    have e2 : (((g m j : ℚ) * (2 * ρ) : ℚ) : ℝ) = (g m j : ℝ) * (2 * (ρ : ℝ)) := by push_cast; ring
    rw [e2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (ρ : ℝ))] at this
    exact this
  set K : ℤ := ⌈B / (2 * (ρ : ℝ))⌉ with hK
  have hgK : ∀ m j, g m j ∈ Finset.Icc (-K) K := by
    intro m j
    have hρ' : (0 : ℝ) < 2 * (ρ : ℝ) := by positivity
    have h1 : |(g m j : ℝ)| ≤ B / (2 * (ρ : ℝ)) := by rw [le_div_iff₀ hρ']; exact hcoef m j
    have h2 : ((|g m j| : ℤ) : ℝ) ≤ (K : ℝ) := by
      rw [Int.cast_abs]; exact le_trans h1 (Int.le_ceil _)
    have h3 : |g m j| ≤ K := by exact_mod_cast h2
    exact Finset.mem_Icc.mpr (abs_le.mp h3)
  let G : ℕ → (Fin n → (Finset.Icc (-K) K)) := fun m j => ⟨g m j, hgK m j⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber G
  have hyinf : (G ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  set w : Fin n → ℤ := fun j => (y j : ℤ) with hw
  have hGw : ∀ m, G m = y → g m = w := by
    intro m hm; funext j; rw [hw]; simp only; rw [← hm]
  obtain ⟨m0, hm0, -⟩ := hyinf.exists_gt 0
  refine ⟨w, by rw [← hGw m0 hm0]; exact hg0 m0, ?_⟩
  intro x hx x' hx'
  obtain ⟨m, hm, hNm⟩ := hyinf.exists_gt ⌈∑ j, |x j| + ∑ j, |x' j|⌉₊
  have hsx : ∀ j, |x j| ≤ ∑ j, |x j| := fun j =>
    Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hsx' : ∀ j, |x' j| ≤ ∑ j, |x' j| := fun j =>
    Finset.single_le_sum (f := fun j => |x' j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hS0 : 0 ≤ ∑ j, |x j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hS0' : 0 ≤ ∑ j, |x' j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hceil : ∑ j, |x j| + ∑ j, |x' j| ≤ (m : ℚ) := by
    have := Nat.le_ceil (∑ j, |x j| + ∑ j, |x' j|)
    have h2 : ((⌈∑ j, |x j| + ∑ j, |x' j|⌉₊ : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hNm.le
    linarith
  have hb : ∀ j, |x j| ≤ max (m : ℚ) R0 := fun j =>
    le_trans (by linarith [hsx j]) (le_max_left _ _)
  have hb' : ∀ j, |x' j| ≤ max (m : ℚ) R0 := fun j =>
    le_trans (by linarith [hsx' j]) (le_max_left _ _)
  rw [← hGw m hm]
  exact hg m x hx hb x' hx' hb'

/-- Child B1 (max-volume simplex rounding; e.g. Schrijver, Theory of Linear and Integer
Programming, proof of Cor. 18.?/Lenstra 1983 §2): a compact convex body contains an affinely
independent simplex such that every point of the body has barycentric coordinates in `[-1,1]`
(take a simplex of maximal volume with vertices in the body). OPEN. -/
def SimplexRounding : Prop :=
  ∀ (n : ℕ) (K : Set (Fin n → ℝ)), IsCompact K → Convex ℝ K → (interior K).Nonempty →
    ∃ v : Fin (n + 1) → (Fin n → ℝ), AffineIndependent ℝ v ∧ (∀ i, v i ∈ K) ∧
      ∀ x ∈ K, ∃ l : Fin (n + 1) → ℝ, ∑ i, l i = 1 ∧ (∀ i, |l i| ≤ 1) ∧ x = ∑ i, l i • v i

/-- Child B2 (flatness for lattice-free simplices; Lenstra 1983 / Kannan–Lovász): the edge
vectors of a lattice-free simplex are all short in some nonzero integral direction. OPEN. -/
def SimplexFlat : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ v : Fin (n + 1) → (Fin n → ℝ), AffineIndependent ℝ v →
    (∀ z : Fin n → ℤ, (fun j => (z j : ℝ)) ∉ convexHull ℝ (Set.range v)) →
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ i, |(fun j => (w j : ℝ)) ⬝ᵥ (v i - v 0)| ≤
      ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) / 2

/-- Child B3: the bounded case follows from simplex rounding (B1) and flatness of lattice-free
simplices (B2): every point of the real polytope has barycentric coordinates in `[-1,1]`, so
widths are at most `2n` times the edge bound. -/
theorem coreBox_of_children (hB1 : SimplexRounding) (hB2 : SimplexFlat) : CoreBox := by
  classical
  unfold CoreBox
  intro n hn k D d R hPZ
  set B : ℝ := ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) with hB
  have hBnn : 0 ≤ B := by positivity
  let D' : Matrix (Fin k ⊕ (Fin n ⊕ Fin n)) (Fin n) ℚ :=
    Matrix.of (Sum.elim (fun i => D i) (Sum.elim (fun j => Pi.single j 1) (fun j => -Pi.single j 1)))
  let d' : Fin k ⊕ (Fin n ⊕ Fin n) → ℚ := Sum.elim d (fun _ => R)
  have hrow1 : ∀ x i, (D' *ᵥ x) (Sum.inl i) = (D *ᵥ x) i := by
    intro x i; simp [D', Matrix.mulVec]
  have hrow2 : ∀ x j, (D' *ᵥ x) (Sum.inr (Sum.inl j)) = x j := by
    intro x j; simp [D', Matrix.mulVec, dotProduct, Pi.single_apply]
  have hrow3 : ∀ x j, (D' *ᵥ x) (Sum.inr (Sum.inr j)) = - x j := by
    intro x j; simp [D', Matrix.mulVec, dotProduct, Pi.single_apply]
  have hD' : ∀ x, D' *ᵥ x ≤ d' ↔ (D *ᵥ x ≤ d ∧ ∀ j, |x j| ≤ R) := by
    intro x
    constructor
    · intro h
      refine ⟨fun i => ?_, fun j => abs_le.mpr ⟨?_, ?_⟩⟩
      · have := h (Sum.inl i); rw [hrow1] at this; exact this
      · have := h (Sum.inr (Sum.inr j)); rw [hrow3] at this
        simp only [d', Sum.elim_inr] at this; linarith
      · have := h (Sum.inr (Sum.inl j)); rw [hrow2] at this
        simp only [d', Sum.elim_inr] at this; exact this
    · rintro ⟨h1, h2⟩ i
      rcases i with i | j | j
      · rw [hrow1]; exact h1 i
      · rw [hrow2]; exact (abs_le.mp (h2 j)).2
      · rw [hrow3]; simp only [d', Sum.elim_inr]; linarith [(abs_le.mp (h2 j)).1]
  by_cases hne : ∃ x, D *ᵥ x ≤ d ∧ ∀ j, |x j| ≤ R
  swap
  · refine ⟨Pi.single ⟨0, hn⟩ 1, ?_, ?_⟩
    · intro h; have := congrFun h ⟨0, hn⟩; simp at this
    · intro x hx hxR; exact absurd ⟨x, hx, hxR⟩ hne
  by_cases hint : ∃ c : Fin n → ℚ, ∀ i, D' i ≠ 0 → (D' *ᵥ c) i < d' i
  swap
  · obtain ⟨w, hw0, hw⟩ := flat_of_no_interior D' d'
      (by obtain ⟨x, hx⟩ := hne; exact ⟨x, (hD' x).2 hx⟩) hint
    refine ⟨w, hw0, fun x hx hxR x' hx' hx'R => ?_⟩
    rw [hw x ((hD' x).2 ⟨hx, hxR⟩) x' ((hD' x').2 ⟨hx', hx'R⟩)]; simpa using hBnn
  obtain ⟨c, hc⟩ := hint
  obtain ⟨x0, hx0, -⟩ := hne
  have hc0 : ∀ i, D i = 0 → 0 ≤ d i := by
    intro i hi
    have h1 := hx0 i
    have e : (D *ᵥ x0) i = 0 := by
      rw [show (D *ᵥ x0) i = ∑ j, D i j * x0 j from rfl]
      simp [show ∀ j, D i j = 0 from fun j => congrFun hi j]
    linarith
  have hcD : ∀ i, D i ≠ 0 → (D *ᵥ c) i < d i := by
    intro i hi
    have := hc (Sum.inl i) hi
    rw [hrow1] at this; exact this
  have hcR : ∀ j, |c j| < R := by
    intro j
    have h1 := hc (Sum.inr (Sum.inl j)) (by intro h; have := congrFun h j; simp [D'] at this)
    have h2 := hc (Sum.inr (Sum.inr j)) (by intro h; have := congrFun h j; simp [D'] at this)
    rw [hrow2] at h1; rw [hrow3] at h2
    simp only [d', Sum.elim_inr] at h1 h2
    exact abs_lt.mpr ⟨by linarith, h1⟩
  -- the real polytope
  let K : Set (Fin n → ℝ) :=
    {x | (∀ i, ∑ j, (D i j : ℝ) * x j ≤ (d i : ℝ)) ∧ ∀ j, |x j| ≤ (R : ℝ)}
  have hcast : ∀ x : Fin n → ℚ, (D *ᵥ x ≤ d ∧ ∀ j, |x j| ≤ R) ↔ (fun j => (x j : ℝ)) ∈ K := by
    intro x
    have e : ∀ i, ∑ j, (D i j : ℝ) * (x j : ℝ) = (((D *ᵥ x) i : ℚ) : ℝ) := by
      intro i; simp [Matrix.mulVec, dotProduct]
    simp only [K, Set.mem_setOf_eq, e]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun i => by exact_mod_cast h1 i, fun j => by exact_mod_cast h2 j⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun i => by exact_mod_cast h1 i, fun j => by exact_mod_cast h2 j⟩
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have : K = {x : Fin n → ℝ | ∀ i, ∑ j, (D i j : ℝ) * x j ≤ (d i : ℝ)} ∩
          {x | ∀ j, |x j| ≤ (R : ℝ)} := rfl
      rw [this]
      refine IsClosed.inter ?_ ?_
      · rw [Set.setOf_forall]
        exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
      · rw [Set.setOf_forall]
        exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨|(R : ℝ)|, fun x hx => ?_⟩
      obtain ⟨-, hx2⟩ := hx
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro j; rw [Real.norm_eq_abs]; exact le_trans (hx2 j) (le_abs_self _)
  have hKconv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have e : ∑ j, (D i j : ℝ) * (a • x + b • y) j =
          a * ∑ j, (D i j : ℝ) * x j + b * ∑ j, (D i j : ℝ) * y j := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      have t1 := mul_le_mul_of_nonneg_left (hx1 i) ha
      have t2 := mul_le_mul_of_nonneg_left (hy1 i) hb
      calc _ ≤ a * (d i : ℝ) + b * (d i : ℝ) := by linarith
        _ = (d i : ℝ) := by rw [← add_mul, hab, one_mul]
    · have t1 := mul_le_mul_of_nonneg_left (hx2 j) ha
      have t2 := mul_le_mul_of_nonneg_left (hy2 j) hb
      calc |(a • x + b • y) j| ≤ a * |x j| + b * |y j| := by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            calc |a * x j + b * y j| ≤ |a * x j| + |b * y j| := abs_add_le _ _
              _ = a * |x j| + b * |y j| := by
                rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * (R : ℝ) + b * (R : ℝ) := by linarith
        _ = (R : ℝ) := by rw [← add_mul, hab, one_mul]
  have hcK : (fun j => (c j : ℝ)) ∈ interior K := by
    let U : Set (Fin n → ℝ) :=
      {x | (∀ i, D i ≠ 0 → ∑ j, (D i j : ℝ) * x j < (d i : ℝ)) ∧ ∀ j, |x j| < (R : ℝ)}
    have hUo : IsOpen U := by
      have : U = {x : Fin n → ℝ | ∀ i, D i ≠ 0 → ∑ j, (D i j : ℝ) * x j < (d i : ℝ)} ∩
          {x | ∀ j, |x j| < (R : ℝ)} := rfl
      rw [this]
      refine IsOpen.inter ?_ ?_
      · rw [Set.setOf_forall]
        refine isOpen_iInter_of_finite fun i => ?_
        by_cases hi : D i = 0
        · simp [hi]
        · simp only [ne_eq, hi, not_false_eq_true, forall_const]
          exact isOpen_lt (by fun_prop) continuous_const
      · rw [Set.setOf_forall]
        exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
    have hUK : U ⊆ K := by
      rintro x ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun j => (h2 j).le⟩
      by_cases hi : D i = 0
      · have h0 : ∀ j, D i j = 0 := fun j => congrFun hi j
        simp only [h0, Rat.cast_zero, zero_mul, Finset.sum_const_zero]
        exact_mod_cast hc0 i hi
      · exact (h1 i hi).le
    have hcU : (fun j => (c j : ℝ)) ∈ U := by
      refine ⟨fun i hi => ?_, fun j => ?_⟩
      · show ∑ j, (D i j : ℝ) * (c j : ℝ) < (d i : ℝ)
        have e : ∑ j, (D i j : ℝ) * (c j : ℝ) = (((D *ᵥ c) i : ℚ) : ℝ) := by
          simp [Matrix.mulVec, dotProduct]
        rw [e]; exact_mod_cast hcD i hi
      · show |(c j : ℝ)| < (R : ℝ)
        exact_mod_cast hcR j
    exact interior_maximal hUK hUo hcU
  have hKZ : ∀ z : Fin n → ℤ, (fun j => (z j : ℝ)) ∉ K := by
    intro z hz
    have hz' : (fun j => (((z j : ℚ)) : ℝ)) ∈ K := by simpa using hz
    obtain ⟨h1, h2⟩ := (hcast (fun j => (z j : ℚ))).2 hz'
    exact hPZ _ h1 h2 (fun i => ⟨z i, rfl⟩)
  obtain ⟨v, hvai, hvK, hbar⟩ := hB1 n K hKc hKconv ⟨_, hcK⟩
  have hhull : convexHull ℝ (Set.range v) ⊆ K :=
    convexHull_min (Set.range_subset_iff.mpr hvK) hKconv
  obtain ⟨w, hw0, hwv⟩ := hB2 n hn v hvai (fun z hz => hKZ z (hhull hz))
  refine ⟨w, hw0, fun x hx hxR x' hx' hx'R => ?_⟩
  obtain ⟨l, hl1, hlb, hlx⟩ := hbar _ ((hcast x).1 ⟨hx, hxR⟩)
  obtain ⟨l', hl1', hlb', hlx'⟩ := hbar _ ((hcast x').1 ⟨hx', hx'R⟩)
  set W : Fin n → ℝ := fun j => (w j : ℝ) with hW
  set C : ℝ := ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) / 2 with hC
  have hval : ((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ) =
      ∑ i, (l i - l' i) * (W ⬝ᵥ (v i - v 0)) := by
    have e1 : ((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ) =
        W ⬝ᵥ ((fun j => (x j : ℝ)) - (fun j => (x' j : ℝ))) := by
      simp [W, dotProduct]
    rw [e1, hlx, hlx']
    have hsum0 : ∑ i, (l i - l' i) = 0 := by rw [Finset.sum_sub_distrib, hl1, hl1', sub_self]
    have e2 : ∀ i, (l i - l' i) * (W ⬝ᵥ (v i - v 0)) =
        (l i - l' i) * (W ⬝ᵥ v i) - (l i - l' i) * (W ⬝ᵥ v 0) := by
      intro i; rw [dotProduct_sub]; ring
    rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0,
      zero_mul, sub_zero, ← Finset.sum_sub_distrib, dotProduct_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← sub_smul, dotProduct_smul, smul_eq_mul]
  rw [hval, Fin.sum_univ_succ]
  simp only [sub_self, dotProduct_zero, mul_zero, zero_add]
  calc |∑ i : Fin n, (l i.succ - l' i.succ) * (W ⬝ᵥ (v i.succ - v 0))|
      ≤ ∑ i : Fin n, |(l i.succ - l' i.succ) * (W ⬝ᵥ (v i.succ - v 0))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * C := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        have a1 := abs_le.mp (hlb i.succ)
        have a2 := abs_le.mp (hlb' i.succ)
        have h1 : |l i.succ - l' i.succ| ≤ 2 := by
          rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
        exact mul_le_mul h1 (hwv i.succ) (abs_nonneg _) (by norm_num)
    _ = B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [hB, hC]; push_cast; ring

/-- The `(n+1) × (n+1)` matrix whose `i`-th column is `(1, v i)`. -/
def homMat {n : ℕ} (v : Fin (n + 1) → (Fin n → ℝ)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun r i => (Fin.cons (1 : ℝ) (v i) : Fin (n + 1) → ℝ) r

lemma homMat_mulVec_zero {n : ℕ} (v : Fin (n + 1) → (Fin n → ℝ)) (μ : Fin (n + 1) → ℝ) :
    (homMat v *ᵥ μ) 0 = ∑ i, μ i := by
  simp [homMat, Matrix.mulVec, dotProduct]

lemma homMat_mulVec_succ {n : ℕ} (v : Fin (n + 1) → (Fin n → ℝ)) (μ : Fin (n + 1) → ℝ)
    (j : Fin n) : (homMat v *ᵥ μ) j.succ = (∑ i, μ i • v i) j := by
  simp [homMat, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma homMat_det_continuous (n : ℕ) :
    Continuous fun v : Fin (n + 1) → (Fin n → ℝ) => (homMat v).det := by
  have : Continuous fun v : Fin (n + 1) → (Fin n → ℝ) => homMat v := by
    refine continuous_matrix fun r i => ?_
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨j, rfl⟩
    · simp only [homMat, Matrix.of_apply, Fin.cons_zero]; exact continuous_const
    · simp only [homMat, Matrix.of_apply, Fin.cons_succ]
      exact (continuous_apply j).comp (continuous_apply i)
  exact this.matrix_det

lemma homMat_update {n : ℕ} (v : Fin (n + 1) → (Fin n → ℝ)) (i : Fin (n + 1))
    (x : Fin n → ℝ) :
    homMat (Function.update v i x) = (homMat v).updateCol i (Fin.cons (1 : ℝ) x) := by
  ext r i'
  by_cases h : i' = i
  · subst h; simp [homMat, Matrix.updateCol_apply]
  · simp [homMat, Matrix.updateCol_apply, h, Function.update_of_ne h]

lemma det_updateCol_mulVec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (l : Fin m → ℝ)
    (i : Fin m) : (A.updateCol i (A *ᵥ l)).det = A.det * l i := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]

/-- Child B1 proved: a maximal-|det| simplex in a compact convex body with interior. -/
theorem simplexRounding : SimplexRounding := by
  classical
  unfold SimplexRounding
  intro n K hKc hKconv hKint
  obtain ⟨c, hc⟩ := hKint
  have hSc : IsCompact (Set.univ.pi fun _ : Fin (n + 1) => K) := isCompact_univ_pi fun _ => hKc
  have hcK : c ∈ K := interior_subset hc
  have hSne : (Set.univ.pi fun _ : Fin (n + 1) => K).Nonempty :=
    ⟨fun _ => c, Set.mem_univ_pi.mpr fun _ => hcK⟩
  have hcont : Continuous fun v : Fin (n + 1) → (Fin n → ℝ) => |(homMat v).det| :=
    (homMat_det_continuous n).abs
  obtain ⟨v, hvS, hvmax⟩ := hSc.exists_isMaxOn hSne hcont.continuousOn
  have hvK : ∀ i, v i ∈ K := fun i => Set.mem_univ_pi.mp hvS i
  have hmax : ∀ u : Fin (n + 1) → (Fin n → ℝ), (∀ i, u i ∈ K) →
      |(homMat u).det| ≤ |(homMat v).det| :=
    fun u hu => isMaxOn_iff.mp hvmax u (Set.mem_univ_pi.mpr hu)
  -- a nondegenerate simplex inside `K`
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc)
  have hδpos : 0 < ε / 2 := by positivity
  let v' : Fin (n + 1) → (Fin n → ℝ) :=
    Fin.cons c (fun j => c + (ε / 2) • (Pi.single j (1 : ℝ) : Fin n → ℝ))
  have hv'K : ∀ i, v' i ∈ K := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simpa [v'] using hcK
    · apply hball
      simp only [v', Fin.cons_succ]
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro k
      rw [Real.dist_eq, Pi.add_apply, add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k = j
      · subst hk
        simp only [Pi.single_eq_same, mul_one, abs_of_pos hδpos]; linarith
      · simp only [Pi.single_eq_of_ne hk, mul_zero, abs_zero]; exact hε
  have hv'det : (homMat v').det ≠ 0 := by
    intro h0
    obtain ⟨μ, hμ0, hμ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hμ0
    have hs : ∑ i, μ i = 0 := by
      have := homMat_mulVec_zero v' μ; rw [hμ] at this; simpa using this.symm
    have hsucc : ∀ k : Fin n, μ k.succ = 0 := by
      intro k
      have h1 : (∑ i, μ i • v' i) k = 0 := by
        have := homMat_mulVec_succ v' μ k; rw [hμ] at this; simpa using this.symm
      have key : (∑ i, μ i • v' i) k = (∑ i, μ i) * c k + (ε / 2) * μ k.succ := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, v',
          Fin.cons_zero, Fin.cons_succ, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_mul,
          Finset.sum_mul]
        have e : ∑ j : Fin n, μ j.succ * (ε / 2 * (Pi.single j (1 : ℝ) : Fin n → ℝ) k) =
            ε / 2 * μ k.succ := by
          rw [Finset.sum_eq_single k]
          · simp only [Pi.single_eq_same, mul_one]; ring
          · intro j _ hj; simp only [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
          · intro h; exact absurd (Finset.mem_univ k) h
        rw [e]; ring
      rw [key, hs, zero_mul, zero_add] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact h
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · rw [Fin.sum_univ_succ] at hs
      simp only [hsucc, Finset.sum_const_zero, add_zero] at hs
      exact hs
    · exact hsucc k
  have hdet0 : (homMat v).det ≠ 0 := by
    intro h0
    have := hmax v' hv'K
    rw [h0, abs_zero] at this
    exact hv'det (abs_nonpos_iff.mp this)
  refine ⟨v, ?_, hvK, ?_⟩
  · rw [affineIndependent_iff_of_fintype]
    intro w hw hwv i
    have hsum : ∑ i, w i • v i = 0 := by
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw 0,
        Finset.weightedVSubOfPoint_apply] at hwv
      simpa [vsub_eq_sub] using hwv
    have hz : homMat v *ᵥ w = 0 := by
      funext r
      rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨j, rfl⟩
      · rw [homMat_mulVec_zero]; exact hw
      · rw [homMat_mulVec_succ, hsum]; rfl
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet0 hz) i
  · intro x hx
    have hU : IsUnit (homMat v).det := isUnit_iff_ne_zero.mpr hdet0
    set l := (homMat v)⁻¹ *ᵥ (Fin.cons (1 : ℝ) x : Fin (n + 1) → ℝ) with hl
    have hAl : homMat v *ᵥ l = Fin.cons (1 : ℝ) x := by
      rw [hl, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    refine ⟨l, ?_, fun i => ?_, ?_⟩
    · have := homMat_mulVec_zero v l; rw [hAl] at this; simpa using this.symm
    · have hdet := det_updateCol_mulVec (homMat v) l i
      rw [hAl, ← homMat_update] at hdet
      have hle := hmax (Function.update v i x) (by
        intro j
        by_cases hj : j = i
        · subst hj; simpa using hx
        · rw [Function.update_of_ne hj]; exact hvK j)
      rw [hdet, abs_mul] at hle
      have hpos : 0 < |(homMat v).det| := abs_pos.mpr hdet0
      by_contra hcon
      push Not at hcon
      nlinarith
    · funext j
      have := homMat_mulVec_succ v l j
      rw [hAl] at this
      simpa using this


/-- Flatness for compact convex lattice-free bodies with width bound `F` (the induction
statement for the hard core). -/
def BodyFlat (n : ℕ) (F : ℝ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
    (∀ z : Fin n → ℤ, (fun j => (z j : ℝ)) ∉ K) →
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ x ∈ K, ∀ x' ∈ K, |(fun j => (w j : ℝ)) ⬝ᵥ (x - x')| ≤ F

lemma bodyFlat_mono {n : ℕ} {F F' : ℝ} (h : BodyFlat n F) (hF : F ≤ F') : BodyFlat n F' := by
  intro K h1 h2 h3 h4
  obtain ⟨w, hw0, hw⟩ := h K h1 h2 h3 h4
  exact ⟨w, hw0, fun x hx x' hx' => le_trans (hw x hx x' hx') hF⟩

/-- The parent's bounded case from flatness of bodies (real polytope construction as in B3). -/
theorem coreBox_of_bodyFlat (hBF : ∀ n, 1 ≤ n →
    BodyFlat n (((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2))) : CoreBox := by
  classical
  unfold CoreBox
  intro n hn k D d R hPZ
  set B : ℝ := ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) with hB
  have hBnn : 0 ≤ B := by positivity
  let D' : Matrix (Fin k ⊕ (Fin n ⊕ Fin n)) (Fin n) ℚ :=
    Matrix.of (Sum.elim (fun i => D i) (Sum.elim (fun j => Pi.single j 1) (fun j => -Pi.single j 1)))
  let d' : Fin k ⊕ (Fin n ⊕ Fin n) → ℚ := Sum.elim d (fun _ => R)
  have hrow1 : ∀ x i, (D' *ᵥ x) (Sum.inl i) = (D *ᵥ x) i := by
    intro x i; simp [D', Matrix.mulVec]
  have hrow2 : ∀ x j, (D' *ᵥ x) (Sum.inr (Sum.inl j)) = x j := by
    intro x j; simp [D', Matrix.mulVec, dotProduct, Pi.single_apply]
  have hrow3 : ∀ x j, (D' *ᵥ x) (Sum.inr (Sum.inr j)) = - x j := by
    intro x j; simp [D', Matrix.mulVec, dotProduct, Pi.single_apply]
  have hD' : ∀ x, D' *ᵥ x ≤ d' ↔ (D *ᵥ x ≤ d ∧ ∀ j, |x j| ≤ R) := by
    intro x
    constructor
    · intro h
      refine ⟨fun i => ?_, fun j => abs_le.mpr ⟨?_, ?_⟩⟩
      · have := h (Sum.inl i); rw [hrow1] at this; exact this
      · have := h (Sum.inr (Sum.inr j)); rw [hrow3] at this
        simp only [d', Sum.elim_inr] at this; linarith
      · have := h (Sum.inr (Sum.inl j)); rw [hrow2] at this
        simp only [d', Sum.elim_inr] at this; exact this
    · rintro ⟨h1, h2⟩ i
      rcases i with i | j | j
      · rw [hrow1]; exact h1 i
      · rw [hrow2]; exact (abs_le.mp (h2 j)).2
      · rw [hrow3]; simp only [d', Sum.elim_inr]; linarith [(abs_le.mp (h2 j)).1]
  by_cases hne : ∃ x, D *ᵥ x ≤ d ∧ ∀ j, |x j| ≤ R
  swap
  · refine ⟨Pi.single ⟨0, hn⟩ 1, ?_, ?_⟩
    · intro h; have := congrFun h ⟨0, hn⟩; simp at this
    · intro x hx hxR; exact absurd ⟨x, hx, hxR⟩ hne
  by_cases hint : ∃ c : Fin n → ℚ, ∀ i, D' i ≠ 0 → (D' *ᵥ c) i < d' i
  swap
  · obtain ⟨w, hw0, hw⟩ := flat_of_no_interior D' d'
      (by obtain ⟨x, hx⟩ := hne; exact ⟨x, (hD' x).2 hx⟩) hint
    refine ⟨w, hw0, fun x hx hxR x' hx' hx'R => ?_⟩
    rw [hw x ((hD' x).2 ⟨hx, hxR⟩) x' ((hD' x').2 ⟨hx', hx'R⟩)]; simpa using hBnn
  obtain ⟨c, hc⟩ := hint
  obtain ⟨x0, hx0, -⟩ := hne
  have hc0 : ∀ i, D i = 0 → 0 ≤ d i := by
    intro i hi
    have h1 := hx0 i
    have e : (D *ᵥ x0) i = 0 := by
      rw [show (D *ᵥ x0) i = ∑ j, D i j * x0 j from rfl]
      simp [show ∀ j, D i j = 0 from fun j => congrFun hi j]
    linarith
  have hcD : ∀ i, D i ≠ 0 → (D *ᵥ c) i < d i := by
    intro i hi
    have := hc (Sum.inl i) hi
    rw [hrow1] at this; exact this
  have hcR : ∀ j, |c j| < R := by
    intro j
    have h1 := hc (Sum.inr (Sum.inl j)) (by intro h; have := congrFun h j; simp [D'] at this)
    have h2 := hc (Sum.inr (Sum.inr j)) (by intro h; have := congrFun h j; simp [D'] at this)
    rw [hrow2] at h1; rw [hrow3] at h2
    simp only [d', Sum.elim_inr] at h1 h2
    exact abs_lt.mpr ⟨by linarith, h1⟩
  -- the real polytope
  let K : Set (Fin n → ℝ) :=
    {x | (∀ i, ∑ j, (D i j : ℝ) * x j ≤ (d i : ℝ)) ∧ ∀ j, |x j| ≤ (R : ℝ)}
  have hcast : ∀ x : Fin n → ℚ, (D *ᵥ x ≤ d ∧ ∀ j, |x j| ≤ R) ↔ (fun j => (x j : ℝ)) ∈ K := by
    intro x
    have e : ∀ i, ∑ j, (D i j : ℝ) * (x j : ℝ) = (((D *ᵥ x) i : ℚ) : ℝ) := by
      intro i; simp [Matrix.mulVec, dotProduct]
    simp only [K, Set.mem_setOf_eq, e]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun i => by exact_mod_cast h1 i, fun j => by exact_mod_cast h2 j⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun i => by exact_mod_cast h1 i, fun j => by exact_mod_cast h2 j⟩
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have : K = {x : Fin n → ℝ | ∀ i, ∑ j, (D i j : ℝ) * x j ≤ (d i : ℝ)} ∩
          {x | ∀ j, |x j| ≤ (R : ℝ)} := rfl
      rw [this]
      refine IsClosed.inter ?_ ?_
      · rw [Set.setOf_forall]
        exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
      · rw [Set.setOf_forall]
        exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨|(R : ℝ)|, fun x hx => ?_⟩
      obtain ⟨-, hx2⟩ := hx
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro j; rw [Real.norm_eq_abs]; exact le_trans (hx2 j) (le_abs_self _)
  have hKconv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have e : ∑ j, (D i j : ℝ) * (a • x + b • y) j =
          a * ∑ j, (D i j : ℝ) * x j + b * ∑ j, (D i j : ℝ) * y j := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      have t1 := mul_le_mul_of_nonneg_left (hx1 i) ha
      have t2 := mul_le_mul_of_nonneg_left (hy1 i) hb
      calc _ ≤ a * (d i : ℝ) + b * (d i : ℝ) := by linarith
        _ = (d i : ℝ) := by rw [← add_mul, hab, one_mul]
    · have t1 := mul_le_mul_of_nonneg_left (hx2 j) ha
      have t2 := mul_le_mul_of_nonneg_left (hy2 j) hb
      calc |(a • x + b • y) j| ≤ a * |x j| + b * |y j| := by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            calc |a * x j + b * y j| ≤ |a * x j| + |b * y j| := abs_add_le _ _
              _ = a * |x j| + b * |y j| := by
                rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * (R : ℝ) + b * (R : ℝ) := by linarith
        _ = (R : ℝ) := by rw [← add_mul, hab, one_mul]
  have hcK : (fun j => (c j : ℝ)) ∈ interior K := by
    let U : Set (Fin n → ℝ) :=
      {x | (∀ i, D i ≠ 0 → ∑ j, (D i j : ℝ) * x j < (d i : ℝ)) ∧ ∀ j, |x j| < (R : ℝ)}
    have hUo : IsOpen U := by
      have : U = {x : Fin n → ℝ | ∀ i, D i ≠ 0 → ∑ j, (D i j : ℝ) * x j < (d i : ℝ)} ∩
          {x | ∀ j, |x j| < (R : ℝ)} := rfl
      rw [this]
      refine IsOpen.inter ?_ ?_
      · rw [Set.setOf_forall]
        refine isOpen_iInter_of_finite fun i => ?_
        by_cases hi : D i = 0
        · simp [hi]
        · simp only [ne_eq, hi, not_false_eq_true, forall_const]
          exact isOpen_lt (by fun_prop) continuous_const
      · rw [Set.setOf_forall]
        exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
    have hUK : U ⊆ K := by
      rintro x ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun j => (h2 j).le⟩
      by_cases hi : D i = 0
      · have h0 : ∀ j, D i j = 0 := fun j => congrFun hi j
        simp only [h0, Rat.cast_zero, zero_mul, Finset.sum_const_zero]
        exact_mod_cast hc0 i hi
      · exact (h1 i hi).le
    have hcU : (fun j => (c j : ℝ)) ∈ U := by
      refine ⟨fun i hi => ?_, fun j => ?_⟩
      · show ∑ j, (D i j : ℝ) * (c j : ℝ) < (d i : ℝ)
        have e : ∑ j, (D i j : ℝ) * (c j : ℝ) = (((D *ᵥ c) i : ℚ) : ℝ) := by
          simp [Matrix.mulVec, dotProduct]
        rw [e]; exact_mod_cast hcD i hi
      · show |(c j : ℝ)| < (R : ℝ)
        exact_mod_cast hcR j
    exact interior_maximal hUK hUo hcU
  have hKZ : ∀ z : Fin n → ℤ, (fun j => (z j : ℝ)) ∉ K := by
    intro z hz
    have hz' : (fun j => (((z j : ℚ)) : ℝ)) ∈ K := by simpa using hz
    obtain ⟨h1, h2⟩ := (hcast (fun j => (z j : ℚ))).2 hz'
    exact hPZ _ h1 h2 (fun i => ⟨z i, rfl⟩)
  obtain ⟨w, hw0, hw⟩ := hBF n hn K hKc hKconv ⟨_, hcK⟩ hKZ
  refine ⟨w, hw0, fun x hx hxR x' hx' hx'R => ?_⟩
  have e1 : ((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ) =
      (fun j => (w j : ℝ)) ⬝ᵥ ((fun j => (x j : ℝ)) - (fun j => (x' j : ℝ))) := by
    simp [dotProduct]
  rw [e1]
  exact hw _ ((hcast x).1 ⟨hx, hxR⟩) _ ((hcast x').1 ⟨hx', hx'R⟩)

/-- Base case `n = 1`: a lattice-free interval has length `< 1`. -/
lemma bodyFlat_one : BodyFlat 1 1 := by
  intro K _ hKconv _ hKZ
  refine ⟨fun _ => 1, by intro h; have := congrFun h 0; simp at this, ?_⟩
  have key : ∀ x ∈ K, ∀ x' ∈ K, x 0 ≤ x' 0 → x' 0 - x 0 ≤ 1 := by
    intro x hx x' hx' hle
    by_contra hcon
    push Not at hcon
    set m : ℤ := ⌈x 0⌉ with hm
    have h1 : x 0 ≤ (m : ℝ) := Int.le_ceil _
    have h2 : (m : ℝ) < x 0 + 1 := Int.ceil_lt_add_one _
    have hpos : 0 < x' 0 - x 0 := by linarith
    set t : ℝ := ((m : ℝ) - x 0) / (x' 0 - x 0) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
    have hmem : (1 - t) • x + t • x' ∈ K :=
      hKconv hx hx' (by linarith) ht0 (by ring)
    apply hKZ (fun _ => m)
    convert hmem using 1
    funext j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht]; field_simp; ring
  intro x hx x' hx'
  have e : (fun _ : Fin 1 => ((1 : ℤ) : ℝ)) ⬝ᵥ (x - x') = x 0 - x' 0 := by
    simp [dotProduct]
  rw [e, abs_le]
  rcases le_total (x 0) (x' 0) with h | h
  · have := key x hx x' hx' h; constructor <;> linarith
  · have := key x' hx' x hx h; constructor <;> linarith

/-- The width bound produced by the induction. -/
noncomputable def Fb : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (n + 2) => max (4 * ((n + 2 : ℕ) : ℝ) ^ 2) ((4 * ((n + 2 : ℕ) : ℝ) + 2) * Fb (n + 1))

/-- Child B2a (Minkowski's convex body theorem for the cube pulled back by `M`): OPEN.
Mathlib: `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`,
`ZSpan.isAddFundamentalDomain` for `Pi.basisFun`, `Measure.addHaar_preimage_linearMap`. -/
def MinkCube : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ), 0 < c → M.det ≠ 0 → |M.det| ≤ c ^ n →
    ∃ z : Fin n → ℤ, z ≠ 0 ∧ ∀ i, |(M *ᵥ fun j => (z j : ℝ)) i| ≤ c

open MeasureTheory in
/-- Child B2a proved (Minkowski for the pulled-back cube). -/
theorem minkCube : MinkCube := by
  intro n hn M c hc hdet hle
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set b := Pi.basisFun ℝ (Fin n) with hb
  have h_fund := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin n → ℝ))
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b))
    infer_instance
  have : DiscreteTopology (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change DiscreteTopology (Submodule.span ℤ (Set.range b))
    infer_instance
  set g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' M⁻¹ with hg
  set s : Set (Fin n → ℝ) := g '' Metric.closedBall 0 c with hs
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨-y, ?_, by simp⟩
    simpa [Metric.mem_closedBall] using hy
  have hconv : Convex ℝ s := (convex_closedBall (0 : Fin n → ℝ) c).linear_image g
  have hcpt : IsCompact s :=
    (isCompact_closedBall (0 : Fin n → ℝ) c).image (LinearMap.continuous_of_finiteDimensional g)
  have hvolF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have : Matrix.of (⇑b) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j; simp [hb, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, abs_one, ENNReal.ofReal_one]
  have hgdet : LinearMap.det g = (M.det)⁻¹ := by
    rw [hg, LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hvols : volume s = ENNReal.ofReal (|M.det|⁻¹ * (2 * c) ^ n) := by
    rw [hs, MeasureTheory.Measure.addHaar_image_linearMap, hgdet,
      Real.volume_pi_closedBall _ hc.le, Fintype.card_fin,
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv]
  have hdetpos : 0 < |M.det| := abs_pos.mpr hdet
  have hineq : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (Fin n → ℝ) ≤ volume s := by
    rw [hvolF, one_mul, hvols, Module.finrank_fin_fun]
    rw [show (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (2 : ℝ) ^ n * |M.det| ≤ 2 ^ n * c ^ n := mul_le_mul_of_nonneg_left hle (by positivity)
    calc (2 : ℝ) ^ n = |M.det|⁻¹ * (2 ^ n * |M.det|) := by
          rw [mul_comm ((2 : ℝ) ^ n) _, ← mul_assoc, inv_mul_cancel₀ hdetpos.ne', one_mul]
      _ ≤ |M.det|⁻¹ * (2 ^ n * c ^ n) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |M.det|⁻¹ * (2 * c) ^ n := by ring
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure h_fund hsymm hconv hcpt hineq
  rw [Submodule.mem_toAddSubgroup, b.mem_span_iff_repr_mem ℤ] at hxL
  choose z hz using hxL
  have hxz : x = fun j => (z j : ℝ) := by
    funext j; simpa [hb] using (hz j).symm
  refine ⟨z, ?_, ?_⟩
  · intro hz0
    apply hx0
    apply Subtype.ext
    show x = (0 : Fin n → ℝ)
    rw [hxz, hz0]; funext j; simp
  · intro i
    obtain ⟨y, hy, hyx⟩ := hxs
    have hyx' : g y = x := hyx
    have hMx : M *ᵥ x = y := by
      rw [← hyx', hg, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
    rw [← hxz, hMx]
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact le_trans (by simpa using norm_le_pi_norm y i) hy

/-- Child B2b (a nonzero integer vector is a multiple of a unimodular image of `e_last`):
OPEN. Route: Smith normal form of `span ℤ {z}` or Euclid by elementary matrices. -/
def UnimodCompletion : Prop :=
  ∀ (n : ℕ) (z : Fin (n + 1) → ℤ), z ≠ 0 → ∃ (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (g : ℤ),
    M * N = 1 ∧ N * M = 1 ∧ 0 < g ∧ M *ᵥ z = Pi.single (Fin.last n) g

/-- Child B2c (induction step; uses `simplexRounding`, `MinkCube`, `UnimodCompletion`): OPEN. -/
def BodyFlatStep : Prop := ∀ n, 1 ≤ n → BodyFlat n (Fb n) → BodyFlat (n + 1) (Fb (n + 1))

/-- Child B2d (numeric): OPEN. -/
def FbBound : Prop := ∀ n, 1 ≤ n → Fb n ≤ ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)

lemma Fb_succ (n : ℕ) (hn : 1 ≤ n) :
    Fb (n + 1) = max (4 * ((n + 1 : ℕ) : ℝ) ^ 2) ((4 * ((n + 1 : ℕ) : ℝ) + 2) * Fb n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

lemma four_mul_le_two_pow (n : ℕ) (hn : 4 ≤ n) : 4 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

lemma Fb_le_sqrt : ∀ n, 1 ≤ n → Fb n ≤ ((n * (n + 1) : ℕ) : ℝ) * Real.sqrt 2 ^ (n ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs14 : (1.4 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by linarith
  have hpow : ∀ k : ℕ, Real.sqrt 2 ^ (2 * k) = 2 ^ k := fun k => by rw [pow_mul, hs2]
  have F1 : Fb 1 = 1 := rfl
  have F2 : Fb 2 = 16 := by rw [Fb_succ 1 le_rfl, F1]; norm_num
  have F3 : Fb 3 = 224 := by rw [Fb_succ 2 (by norm_num), F2]; norm_num
  have F4 : Fb 4 = 4032 := by rw [Fb_succ 3 (by norm_num), F3]; norm_num
  have base4 : Fb 4 ≤ ((4 * (4 + 1) : ℕ) : ℝ) * Real.sqrt 2 ^ (4 ^ 2) := by
    rw [F4, show (4 : ℕ) ^ 2 = 2 * 8 by norm_num, hpow]; norm_num
  have step : ∀ n, 4 ≤ n → Fb n ≤ ((n * (n + 1) : ℕ) : ℝ) * Real.sqrt 2 ^ (n ^ 2) →
      Fb (n + 1) ≤ (((n + 1) * (n + 1 + 1) : ℕ) : ℝ) * Real.sqrt 2 ^ ((n + 1) ^ 2) := by
    intro n hn ih
    rw [Fb_succ n (by omega)]
    have h4n : (4 * n : ℝ) ≤ 2 ^ n := by exact_mod_cast four_mul_le_two_pow n hn
    have hsq : Real.sqrt 2 ^ ((n + 1) ^ 2) = Real.sqrt 2 ^ (n ^ 2) * 2 ^ n * Real.sqrt 2 := by
      rw [show (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 by ring, pow_add, pow_add, hpow, pow_one]
    have hS : (1 : ℝ) ≤ Real.sqrt 2 ^ (n ^ 2) := one_le_pow₀ hs1
    have hS4 : (4 : ℝ) ≤ Real.sqrt 2 ^ ((n + 1) ^ 2) := by
      calc (4 : ℝ) = Real.sqrt 2 ^ (2 * 2) := by rw [hpow]; norm_num
        _ ≤ _ := pow_le_pow_right₀ hs1 (by nlinarith)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    push_cast at ih ⊢
    apply max_le
    · nlinarith
    · rw [hsq]
      set S := Real.sqrt 2 ^ (n ^ 2)
      have hFn : Fb n ≤ n * (n + 1) * S := ih
      have h1 : (4 * (n + 1 : ℝ) + 2) * Fb n ≤ (4 * (n + 1 : ℝ) + 2) * (n * (n + 1) * S) :=
        mul_le_mul_of_nonneg_left hFn (by positivity)
      have h2 : (4 * (n + 1 : ℝ) + 2) * (n * (n + 1) * S) ≤ ((n + 1) * (n + 1 + 1)) * (4 * n) * S := by
        have : (0 : ℝ) ≤ n * (n + 1) * S := by positivity
        nlinarith
      have h3 : ((n + 1 : ℝ) * (n + 1 + 1)) * (4 * n) * S ≤ ((n + 1) * (n + 1 + 1)) * (S * 2 ^ n * Real.sqrt 2) := by
        have hp : (0 : ℝ) ≤ (n + 1) * (n + 1 + 1) := by positivity
        have : (4 * n : ℝ) * S ≤ S * 2 ^ n * Real.sqrt 2 := by
          have hS0 : (0 : ℝ) ≤ S := by positivity
          have : (4 * n : ℝ) * S ≤ 2 ^ n * S := mul_le_mul_of_nonneg_right h4n hS0
          have h2n : (0 : ℝ) ≤ 2 ^ n * S := by positivity
          nlinarith
        nlinarith
      linarith
  intro n hn
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h | h | h | h
  · subst h; rw [F1]; norm_num; linarith
  · subst h; rw [F2, show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, hpow]; norm_num
  · subst h
    rw [F3, show (3 : ℕ) ^ 2 = 2 * 4 + 1 by norm_num, pow_succ, hpow]; norm_num; nlinarith
  · induction n, h using Nat.le_induction with
    | base => exact base4
    | succ k hk ih => exact step k hk (ih (by omega))

theorem fbBound : FbBound := by
  intro n hn
  have h := Fb_le_sqrt n hn
  have e : (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) = Real.sqrt 2 ^ (n ^ 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by norm_num)]
    congr 1; push_cast; ring
  rw [e]; exact h

theorem unimodCompletion : UnimodCompletion := by
  intro n z hz
  classical
  set std := Pi.basisFun ℤ (Fin (n + 1)) with hstd
  obtain ⟨m, S⟩ := Submodule.smithNormalForm std (Submodule.span ℤ {z})
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      subst h
      have hz' : (⟨z, Submodule.mem_span_singleton_self z⟩ : Submodule.span ℤ {z}) = 0 := by
        rw [← S.bN.sum_repr ⟨z, Submodule.mem_span_singleton_self z⟩]
        simp
      exact hz (congrArg Subtype.val hz')
    · exact h
  set i0 : Fin m := ⟨0, hm⟩
  set k := S.f i0
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp (S.bN i0).2
  have hbN0 : (S.bN i0 : Fin (n + 1) → ℤ) ≠ 0 := by
    intro h; exact S.bN.ne_zero i0 (Subtype.ext h)
  have hβ0 : β ≠ 0 := by
    rintro rfl; apply hbN0; rw [← hβ, zero_smul]
  have hsnf := S.snf i0
  have hrep : ∀ j, j ≠ k → S.bM.repr z j = 0 := by
    intro j hj
    have := congrArg (fun v => S.bM.repr v j) (hβ.trans hsnf)
    simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, smul_eq_mul] at this
    rw [Finsupp.single_apply, if_neg (Ne.symm hj), mul_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hβ0
    · exact h
  set t := S.bM.repr z k with ht_def
  have ht : t ≠ 0 := by
    intro h0; apply hz
    have : S.bM.repr z = 0 := by
      ext j
      by_cases hj : j = k
      · subst hj; simpa using h0
      · simpa using hrep j hj
    simpa using this
  set σ := Equiv.swap k (Fin.last n)
  set b' := S.bM.reindex σ
  have hrep' : ∀ i, b'.repr z i = (Pi.single (Fin.last n) t : Fin (n + 1) → ℤ) i := by
    intro i
    rw [Module.Basis.repr_reindex_apply]
    by_cases hi : i = Fin.last n
    · subst hi
      simp [σ, Equiv.symm_swap, Equiv.swap_apply_right, t]
    · rw [Pi.single_apply, if_neg hi]
      apply hrep
      intro h
      apply hi
      have : σ.symm i = k := h
      rw [Equiv.symm_apply_eq] at this
      rw [this]; simp [σ, Equiv.swap_apply_left]
  have hMv : b'.toMatrix std *ᵥ z = Pi.single (Fin.last n) t := by
    have h := Module.Basis.toMatrix_mulVec_repr std b' z
    have hz2 : (⇑(std.repr z) : Fin (n + 1) → ℤ) = z := by
      funext j; simp [hstd]
    rw [hz2] at h
    rw [h]; funext i; exact hrep' i
  have h1 : b'.toMatrix std * std.toMatrix b' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : std.toMatrix b' * b'.toMatrix std = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨-(b'.toMatrix std), -(std.toMatrix b'), -t, by rw [neg_mul_neg, h1],
      by rw [neg_mul_neg, h2], by omega, ?_⟩
    rw [Matrix.neg_mulVec, hMv, Pi.single_neg]
  · exact ⟨b'.toMatrix std, std.toMatrix b', t, h1, h2, hpos, hMv⟩

/-- Child B2c-1 (projection along an integral direction whose unit segments stay in `K`). -/
def ProjStep : Prop :=
  ∀ (n : ℕ) (F : ℝ), BodyFlat n F →
  ∀ (K C : Set (Fin (n + 1) → ℝ)) (z : Fin (n + 1) → ℤ) (lam : ℝ), 0 ≤ lam → z ≠ 0 →
    (∀ y : Fin (n + 1) → ℤ, (fun j => (y j : ℝ)) ∉ K) →
    IsCompact C → Convex ℝ C → (interior C).Nonempty →
    (∀ p ∈ C, ∀ s : ℝ, |s| ≤ 1 / 2 → p + s • (fun j => (z j : ℝ)) ∈ K) →
    (∀ x ∈ K, ∀ x' ∈ K, ∃ c ∈ C, ∃ c' ∈ C, x - x' = lam • (c - c')) →
    ∃ w : Fin (n + 1) → ℤ, w ≠ 0 ∧ ∀ x ∈ K, ∀ x' ∈ K, |(fun j => (w j : ℝ)) ⬝ᵥ (x - x')| ≤ lam * F

theorem projStep (hU : UnimodCompletion) : ProjStep := by
  intro n F hIH K C z lam hlam hz hKfree hCc hCv hCi hseg hdiff
  classical
  obtain ⟨M, N, g, hMN, hNM, hg, hMz⟩ := hU n z hz
  set Mr : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := M.map (Int.castRingHom ℝ) with hMr
  set Nr : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := N.map (Int.castRingHom ℝ) with hNr
  have hcastv : ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (v : Fin (n + 1) → ℤ),
      A.map (Int.castRingHom ℝ) *ᵥ (fun j => (v j : ℝ)) = fun i => ((A *ᵥ v) i : ℝ) := by
    intro A v; funext i
    simp [Matrix.mulVec, dotProduct]
  have hNMr : Nr * Mr = 1 := by
    have := congrArg (Int.castRingHom ℝ).mapMatrix hNM
    rw [map_mul, map_one] at this
    exact this
  have hMNr : Mr * Nr = 1 := by
    have := congrArg (Int.castRingHom ℝ).mapMatrix hMN
    rw [map_mul, map_one] at this
    exact this
  set L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Fin.castSucc).comp (Matrix.toLin' Mr) with hLdef
  have hL : ∀ p i, L p i = (Mr *ᵥ p) (Fin.castSucc i) := by
    intro p i; simp [L, LinearMap.funLeft_apply, Matrix.toLin'_apply]
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨Nr *ᵥ (Fin.snoc y 0 : Fin (n + 1) → ℝ), ?_⟩
    funext i
    rw [hL, Matrix.mulVec_mulVec, hMNr, Matrix.one_mulVec, Fin.snoc_castSucc]
  have hcomp : IsCompact (L '' C) := hCc.image (LinearMap.continuous_of_finiteDimensional L)
  have hconv : Convex ℝ (L '' C) := hCv.linear_image L
  have hint : (interior (L '' C)).Nonempty := by
    obtain ⟨p, hp⟩ := hCi
    exact ⟨L p, interior_maximal (Set.image_mono interior_subset)
      (LinearMap.isOpenMap_of_finiteDimensional L hsurj _ isOpen_interior) ⟨p, hp, rfl⟩⟩
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (show (1 : ℤ) ≤ g by omega)
  have hfree : ∀ y : Fin n → ℤ, (fun j => (y j : ℝ)) ∉ L '' C := by
    rintro y ⟨p, hpC, hpy⟩
    obtain ⟨t, ht⟩ : ∃ t, t = (Mr *ᵥ p) (Fin.last n) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ((round t : ℤ) - t) / g := ⟨_, rfl⟩
    have hsle : |s| ≤ 1 / 2 := by
      have h1 := abs_sub_round t
      rw [hs, abs_div, abs_of_pos (by linarith : (0 : ℝ) < g), div_le_iff₀ (by linarith),
        abs_sub_comm]
      nlinarith [abs_nonneg (t - round t)]
    have hq := hseg p hpC s hsle
    have hMzr : Mr *ᵥ (fun j => (z j : ℝ)) =
        fun i => ((Pi.single (Fin.last n) g : Fin (n + 1) → ℤ) i : ℝ) := by
      rw [hMr, hcastv, hMz]
    have key : Mr *ᵥ (p + s • (fun j => (z j : ℝ))) =
        fun i => ((Fin.snoc y (round t) : Fin (n + 1) → ℤ) i : ℝ) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hMzr]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Pi.add_apply, ← ht, Pi.smul_apply, Pi.single_eq_same, Fin.snoc_last, hs, smul_eq_mul]
        field_simp
        ring
      · have h2 := congrFun hpy i
        rw [hL] at h2
        rw [Pi.add_apply, h2, Pi.smul_apply, Fin.snoc_castSucc,
          Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]
        simp
    have hqint : p + s • (fun j => (z j : ℝ)) = fun j => ((N *ᵥ Fin.snoc y (round t)) j : ℝ) := by
      rw [← hcastv N, ← key, ← hNr, Matrix.mulVec_mulVec, hNMr, Matrix.one_mulVec]
    exact hKfree _ (hqint ▸ hq)
  obtain ⟨w', hw'0, hw'⟩ := hIH (L '' C) hcomp hconv hint hfree
  set u : Fin (n + 1) → ℤ := Fin.snoc w' 0 with hu
  have hwdot : ∀ v : Fin (n + 1) → ℝ,
      (fun j => ((Mᵀ *ᵥ u) j : ℝ)) ⬝ᵥ v = (fun j => (w' j : ℝ)) ⬝ᵥ L v := by
    intro v
    have h1 : (fun j => ((Mᵀ *ᵥ u) j : ℝ)) = Mrᵀ *ᵥ (fun j => (u j : ℝ)) := by
      rw [hMr, ← Matrix.transpose_map, hcastv]
    rw [h1, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp only [dotProduct, Fin.sum_univ_castSucc, hu, Fin.snoc_castSucc, Fin.snoc_last, hL]
    simp [mul_comm]
  refine ⟨Mᵀ *ᵥ u, ?_, ?_⟩
  · intro h0
    have hu0 : u = 0 := by
      have h3 := congrArg (fun a => Nᵀ *ᵥ a) h0
      simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hMN, Matrix.transpose_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h3
      exact h3
    apply hw'0
    funext i
    have := congrFun hu0 (Fin.castSucc i)
    simpa [hu] using this
  · intro x hx x' hx'
    obtain ⟨c, hc, c', hc', hxc⟩ := hdiff x hx x' hx'
    rw [hxc, dotProduct_smul, smul_eq_mul, hwdot, map_sub, abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left (hw' _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩) hlam

lemma bodyFlat_all (hS : BodyFlatStep) : ∀ n, 1 ≤ n → BodyFlat n (Fb n) := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simpa [Fb] using bodyFlat_one
    · exact hS m hpos (ih hpos)

theorem coreBox_of_step (hS : BodyFlatStep) (hB : FbBound) : CoreBox :=
  coreBox_of_bodyFlat fun n hn => bodyFlat_mono (bodyFlat_all hS n hn) (hB n hn)

theorem coreBox_of_bodyFlatStep (hS : BodyFlatStep) : CoreBox := coreBox_of_step hS fbBound


/-! ### Child B2c: the induction step (dual / primal case split on the rounding simplex). -/

lemma Fb_nonneg : ∀ n, 0 ≤ Fb n
  | 0 => by norm_num [Fb]
  | 1 => by norm_num [Fb]
  | (n + 2) => by simp only [Fb]; exact le_max_of_le_left (by positivity)

/-- Edge matrix of a simplex: column `i` is `v (i+1) - v 0`. -/
def Umat {m : ℕ} (v : Fin (m + 1) → (Fin m → ℝ)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j i => (v i.succ - v 0) j

lemma Umat_mulVec {m : ℕ} (v : Fin (m + 1) → (Fin m → ℝ)) (t : Fin m → ℝ) :
    Umat v *ᵥ t = ∑ i, t i • (v i.succ - v 0) := by
  ext j
  simp only [Umat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma rep_of_bary {m : ℕ} (v : Fin (m + 1) → (Fin m → ℝ)) (l : Fin (m + 1) → ℝ)
    (hsum : ∑ i, l i = 1) : ∑ i, l i • v i = v 0 + Umat v *ᵥ (fun i => l i.succ) := by
  rw [Umat_mulVec, Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ] at hsum
  have h0 : l 0 = 1 - ∑ i : Fin m, l i.succ := by linarith
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h0, sub_smul, one_smul]
  abel

lemma simplex_mem {m : ℕ} {K : Set (Fin m → ℝ)} (hK : Convex ℝ K) (v : Fin (m + 1) → (Fin m → ℝ))
    (hv : ∀ i, v i ∈ K) (t : Fin m → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ≤ 1) :
    v 0 + Umat v *ᵥ t ∈ K := by
  set w : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ i, t i) t with hwdef
  have hw1 : ∑ i, w i = 1 := by
    rw [Fin.sum_univ_succ]; simp only [hwdef, Fin.cons_zero, Fin.cons_succ]; ring
  have hwt : (fun i : Fin m => w i.succ) = t := by funext i; simp only [hwdef, Fin.cons_succ]
  have hw := rep_of_bary v w hw1
  rw [hwt] at hw
  rw [← hw]
  apply hK.sum_mem
  · intro i _
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [hwdef, Fin.cons_zero]; linarith
    · simp only [hwdef, Fin.cons_succ]; exact ht0 i
  · exact hw1
  · intro i _; exact hv i

lemma det_ne_zero_of_rep {m : ℕ} {K : Set (Fin m → ℝ)} (U : Matrix (Fin m) (Fin m) ℝ)
    (v0 : Fin m → ℝ) (hrep : ∀ x ∈ K, ∃ μ : Fin m → ℝ, x = v0 + U *ᵥ μ)
    (hi : (interior K).Nonempty) : U.det ≠ 0 := by
  intro hdet
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  obtain ⟨p, hp⟩ := hi
  have hev : ∀ᶠ t in nhds (0 : ℝ), p + t • y ∈ K := by
    have hc : Continuous fun t : ℝ => p + t • y :=
      continuous_const.add (continuous_id.smul continuous_const)
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.eventually_mem (mem_interior_iff_mem_nhds.mp hp)
  have hzero : ∀ x ∈ K, y ⬝ᵥ (x - v0) = 0 := by
    intro x hx
    obtain ⟨μ, rfl⟩ := hrep x hx
    rw [add_sub_cancel_left, dotProduct_mulVec, hy, zero_dotProduct]
  have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, p + t • y ∈ K ∧ t ∈ ({0}ᶜ : Set ℝ) :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ht, ht0⟩ := hev'.exists
  have h1 := hzero _ ht
  have h2 := hzero p (interior_subset hp)
  have e : p + t • y - v0 = (p - v0) + t • y := by abel
  rw [e, dotProduct_add, h2, dotProduct_smul, zero_add, smul_eq_mul] at h1
  have ht0' : t ≠ 0 := by simpa using ht0
  have hyy : y ⬝ᵥ y = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h ht0'
    · exact h
  exact hy0 (dotProduct_self_eq_zero.mp hyy)

lemma dual_case (hM : MinkCube) {m : ℕ} (hm : 1 ≤ m) {K : Set (Fin m → ℝ)}
    (U : Matrix (Fin m) (Fin m) ℝ) (v0 : Fin m → ℝ)
    (hrep : ∀ x ∈ K, ∃ μ : Fin m → ℝ, (∀ i, |μ i| ≤ 1) ∧ x = v0 + U *ᵥ μ)
    (hdet0 : U.det ≠ 0) (hdet : |U.det| ≤ (2 * (m : ℝ)) ^ m) :
    ∃ w : Fin m → ℤ, w ≠ 0 ∧ ∀ x ∈ K, ∀ x' ∈ K,
      |(fun j => (w j : ℝ)) ⬝ᵥ (x - x')| ≤ 4 * (m : ℝ) ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨w, hw0, hw⟩ := hM m hm Uᵀ (2 * m) (by positivity) (by rwa [det_transpose])
    (by rwa [det_transpose])
  refine ⟨w, hw0, fun x hx x' hx' => ?_⟩
  obtain ⟨μ, hμ, rfl⟩ := hrep x hx
  obtain ⟨μ', hμ', rfl⟩ := hrep x' hx'
  have e : v0 + U *ᵥ μ - (v0 + U *ᵥ μ') = U *ᵥ (μ - μ') := by rw [mulVec_sub]; abel
  rw [e, dotProduct_mulVec, ← mulVec_transpose]
  set a := Uᵀ *ᵥ (fun j => (w j : ℝ)) with ha
  calc |a ⬝ᵥ (μ - μ')| ≤ ∑ i, |a i * (μ - μ') i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, (2 * (m : ℝ)) * 2 := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        have h3 := abs_le.mp (hμ i)
        have h4 := abs_le.mp (hμ' i)
        have h2 : |(μ - μ') i| ≤ 2 := by
          rw [Pi.sub_apply, abs_le]; constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
        exact mul_le_mul (hw i) h2 (abs_nonneg _) (by positivity)
    _ = 4 * (m : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma primal_case (hM : MinkCube) (hP : ProjStep) {n : ℕ} {F : ℝ} (hIH : BodyFlat n F)
    {K : Set (Fin (n + 1) → ℝ)} (hKfree : ∀ y : Fin (n + 1) → ℤ, (fun j => (y j : ℝ)) ∉ K)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v0 : Fin (n + 1) → ℝ)
    (hrep : ∀ x ∈ K, ∃ μ : Fin (n + 1) → ℝ, (∀ i, |μ i| ≤ 1) ∧ x = v0 + U *ᵥ μ)
    (hsimp : ∀ t : Fin (n + 1) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i ≤ 1 → v0 + U *ᵥ t ∈ K)
    (hdet0 : U.det ≠ 0) (hdet : (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) < |U.det|) :
    ∃ w : Fin (n + 1) → ℤ, w ≠ 0 ∧ ∀ x ∈ K, ∀ x' ∈ K,
      |(fun j => (w j : ℝ)) ⬝ᵥ (x - x')| ≤ (4 * ((n + 1 : ℕ) : ℝ)) * F := by
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((n + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hN] at hdet ⊢
  have hNpos : 0 < N := by rw [hN]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 / (4 * N) := ⟨_, rfl⟩
  have hqpos : 0 < q := by rw [hq]; positivity
  have hqN : 4 * N * q = 1 := by rw [hq]; field_simp
  have hU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet0
  have hdi : (U⁻¹).det = (U.det)⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have h2q : 2 * q = (2 * N)⁻¹ := by rw [hq]; field_simp; ring
  obtain ⟨z, hz0, hz⟩ := hM (n + 1) (by omega) U⁻¹ (2 * q) (by positivity)
    (by rw [hdi]; exact inv_ne_zero hdet0)
    (by
      rw [hdi, abs_inv, h2q, inv_pow]
      exact (inv_le_inv₀ (abs_pos.mpr hdet0) (by positivity)).mpr hdet.le)
  set zr : Fin (n + 1) → ℝ := fun j => (z j : ℝ) with hzr
  set a : Fin (n + 1) → ℝ := U⁻¹ *ᵥ zr with ha
  have hUa : U *ᵥ a = zr := by rw [ha, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  set B : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun _ => Set.Icc q (3 * q) with hB
  set f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun y => v0 + U *ᵥ y with hf
  set C := f '' B with hC
  have hfc : Continuous f := continuous_const.add (continuous_const.matrix_mulVec continuous_id)
  have hCc : IsCompact C := (isCompact_univ_pi fun _ => isCompact_Icc).image hfc
  have hBv : Convex ℝ B := convex_pi fun _ _ => convex_Icc _ _
  have hCv : Convex ℝ C := by
    rintro _ ⟨y1, hy1, rfl⟩ _ ⟨y2, hy2, rfl⟩ s t hs ht hst
    refine ⟨s • y1 + t • y2, hBv hy1 hy2 hs ht hst, ?_⟩
    ext j
    simp only [hf, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(v0 j)) * hst
  set g : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun x => U⁻¹ *ᵥ (x - v0) with hg
  have hgc : Continuous g := continuous_const.matrix_mulVec (continuous_id.sub continuous_const)
  have hfg : ∀ x, f (g x) = x := by
    intro x; simp only [hf, hg, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]; abel
  have hgf : ∀ y, g (f y) = y := by
    intro y
    simp only [hf, hg, add_sub_cancel_left, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
  set O := g ⁻¹' (Set.univ.pi fun _ => Set.Ioo q (3 * q)) with hO
  have hOopen : IsOpen O := (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage hgc
  have hOC : O ⊆ C := by
    intro x hx
    refine ⟨g x, ?_, hfg x⟩
    exact Set.mem_univ_pi.mpr fun i => Set.Ioo_subset_Icc_self (Set.mem_univ_pi.mp hx i)
  have hCi : (interior C).Nonempty := by
    refine ⟨f (fun _ => 2 * q), interior_maximal hOC hOopen ?_⟩
    rw [hO, Set.mem_preimage, hgf]
    exact Set.mem_univ_pi.mpr fun _ => ⟨by linarith, by linarith⟩
  have hseg : ∀ p ∈ C, ∀ s : ℝ, |s| ≤ 1 / 2 → p + s • zr ∈ K := by
    rintro _ ⟨y, hy, rfl⟩ s hs
    have e : f y + s • zr = v0 + U *ᵥ (y + s • a) := by
      simp only [hf]; rw [mulVec_add, mulVec_smul, hUa, add_assoc]
    rw [e]
    have hbd : ∀ i, 0 ≤ (y + s • a) i ∧ (y + s • a) i ≤ 4 * q := by
      intro i
      have hyi := Set.mem_univ_pi.mp hy i
      have hsa : |s * a i| ≤ q := by
        rw [abs_mul]
        calc |s| * |a i| ≤ 1 / 2 * (2 * q) := mul_le_mul hs (hz i) (abs_nonneg _) (by norm_num)
          _ = q := by ring
      have := abs_le.mp hsa
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      constructor <;> linarith [hyi.1, hyi.2]
    apply hsimp
    · exact fun i => (hbd i).1
    · calc ∑ i, (y + s • a) i ≤ ∑ _i : Fin (n + 1), 4 * q :=
            Finset.sum_le_sum fun i _ => (hbd i).2
        _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hN]
          linear_combination hqN
  have hdiff : ∀ x ∈ K, ∀ x' ∈ K, ∃ c ∈ C, ∃ c' ∈ C, x - x' = (4 * N) • (c - c') := by
    intro x hx x' hx'
    obtain ⟨μ, hμ, rfl⟩ := hrep x hx
    obtain ⟨μ', hμ', rfl⟩ := hrep x' hx'
    set d : Fin (n + 1) → ℝ := fun i => q / 2 * (μ i - μ' i) with hd
    have hdb : ∀ i, |d i| ≤ q := by
      intro i
      have h1 := abs_le.mp (hμ i)
      have h2 := abs_le.mp (hμ' i)
      rw [abs_le]; simp only [hd]
      constructor <;>
        nlinarith [mul_nonneg hqpos.le (by linarith : (0 : ℝ) ≤ 2 - (μ i - μ' i)),
          mul_nonneg hqpos.le (by linarith : (0 : ℝ) ≤ 2 + (μ i - μ' i))]
    have hmem : ∀ e : Fin (n + 1) → ℝ, (∀ i, |e i| ≤ q) → (fun _ => 2 * q) + e ∈ B := by
      intro e he
      exact Set.mem_univ_pi.mpr fun i => by
        have := abs_le.mp (he i); simp only [Pi.add_apply]; constructor <;> linarith
    refine ⟨f ((fun _ => 2 * q) + d), ⟨_, hmem d hdb, rfl⟩, f ((fun _ => 2 * q) + -d),
      ⟨_, hmem (-d) (fun i => by simpa using hdb i), rfl⟩, ?_⟩
    have hdd : (4 * N) • (d + d) = μ - μ' := by
      ext i; simp only [hd, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination (μ i - μ' i) * hqN
    calc v0 + U *ᵥ μ - (v0 + U *ᵥ μ') = U *ᵥ (μ - μ') := by rw [mulVec_sub]; abel
      _ = U *ᵥ ((4 * N) • (d + d)) := by rw [hdd]
      _ = (4 * N) • (f ((fun _ => 2 * q) + d) - f ((fun _ => 2 * q) + -d)) := by
          simp only [hf, mulVec_smul, mulVec_add, mulVec_neg]; congr 1; abel
  exact hP n F hIH K C z (4 * N) (by positivity) hz0 hKfree hCc hCv hCi hseg hdiff

theorem bodyFlatStep_of (hR : SimplexRounding) (hM : MinkCube) (hP : ProjStep) :
    BodyFlatStep := by
  intro n hn hIH K hKc hKv hKi hKfree
  obtain ⟨v, -, hvK, hbary⟩ := hR (n + 1) K hKc hKv hKi
  have hrep : ∀ x ∈ K, ∃ μ : Fin (n + 1) → ℝ, (∀ i, |μ i| ≤ 1) ∧ x = v 0 + Umat v *ᵥ μ := by
    intro x hx
    obtain ⟨l, hl1, hlb, rfl⟩ := hbary x hx
    exact ⟨fun i => l i.succ, fun i => hlb i.succ, rep_of_bary v l hl1⟩
  have hdet0 : (Umat v).det ≠ 0 :=
    det_ne_zero_of_rep (Umat v) (v 0) (fun x hx => (hrep x hx).imp fun μ h => h.2) hKi
  have hF0 : 0 ≤ Fb n := Fb_nonneg n
  rw [Fb_succ n hn]
  rcases le_or_gt |(Umat v).det| ((2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) with h | h
  · obtain ⟨w, hw0, hw⟩ := dual_case hM (by omega) (Umat v) (v 0) hrep hdet0 h
    exact ⟨w, hw0, fun x hx x' hx' => (hw x hx x' hx').trans (le_max_left _ _)⟩
  · obtain ⟨w, hw0, hw⟩ := primal_case hM hP hIH hKfree (Umat v) (v 0) hrep
      (fun t ht0 ht1 => simplex_mem hKv v hvK t ht0 ht1) hdet0 h
    refine ⟨w, hw0, fun x hx x' hx' => (hw x hx x' hx').trans (le_trans ?_ (le_max_right _ _))⟩
    exact mul_le_mul_of_nonneg_right (by linarith) hF0

/-- Child B2c proved: the induction step. -/
theorem bodyFlatStep : BodyFlatStep :=
  bodyFlatStep_of simplexRounding minkCube (projStep unimodCompletion)

end FlatFd3

open CookSensitivity.ChvatalRank Matrix in
theorem solution {n : ℕ} (hn : 1 ≤ n) (P : Set (Fin n → ℚ))
    (hP : IsPolyhedron P) (hPZ : ∀ x ∈ P, ¬ IsIntegral x) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ x ∈ P, ∀ x' ∈ P,
      |((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ)| ≤
        ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) := by
  exact FlatFd3.parent_of_core (FlatFd3.coreBox_of_bodyFlatStep FlatFd3.bodyFlatStep) hn P hP hPZ

