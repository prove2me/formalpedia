-- Prove2me | solution 1 for Disjunctive.CutCorrespondence.strengthened_cut_correspondence_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:22:58.518402+00:00
-- url     : https://prove2.me/submissions/7657dc58-80da-4511-932e-9b49dbcc92fc

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2



namespace Disjunctive.CutCorrespondence

lemma bc_disjoint {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ)
    (β : ℝ) (M1 M2 : Finset M)
    (hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) : Disjoint M1 M2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -⟩ := hf
  rw [Finset.disjoint_left]
  intro ρ hρ1 hρ2
  have key := hbasis.2 (fun i => α i - (1/2) * Atil ρ i)
    (fun r => u r - if r = ρ then 1/2 else 0) u0
    (fun r => v r - if r = ρ then 1/2 else 0) v0 (β - btil ρ / 2)
    (by
      intro i
      have := h1 i
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      intro i
      have := h2 i
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      linarith)
    (by
      intro r hr
      have hne : r ≠ ρ := fun h => hr (h ▸ hρ1)
      simp [hu_supp r hr, hne])
    (by
      intro r hr
      have hne : r ≠ ρ := fun h => hr (h ▸ hρ2)
      simp [hv_supp r hr, hne])
  linarith [key.2.2.1]

/-- Nonsingularity of `Ã_J` for any enumeration of a subset of `M1 ∪ M2`. -/
lemma bc_det {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ)
    (β : ℝ) (M1 M2 : Finset M)
    (hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) (hdisj : Disjoint M1 M2)
    (ι : Fin n → M) (hι : Function.Injective ι) (hιJ : ∀ i, ι i ∈ M1 ∪ M2) :
    IsUnit (Ahat Atil ι).det := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -⟩ := hf
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨y, hy0, hy⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hdet
  -- λ on rows
  set lam : M → ℝ := fun r => ∑ i, if ι i = r then y i else 0 with hlam
  have hsum : ∀ g : M → ℝ, ∑ r, lam r * g r = ∑ i, y i * g (ι i) := by
    intro g
    simp only [hlam, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  have hlamι : ∀ i, lam (ι i) = y i := by
    intro i
    simp only [hlam]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hι.ne hj]
    · simp
  have hlam_out : ∀ r, r ∉ M1 ∪ M2 → lam r = 0 := by
    intro r hr
    simp only [hlam]
    apply Finset.sum_eq_zero
    intro i _
    have : ι i ≠ r := fun h => hr (h ▸ hιJ i)
    simp [this]
  have hlamA : ∀ i, ∑ r, lam r * Atil r i = 0 := by
    intro i
    rw [hsum (fun r => Atil r i)]
    have := congrFun hy i
    simpa [Matrix.vecMul, dotProduct, Ahat] using this
  set l1 : M → ℝ := fun r => if r ∈ M1 then lam r else 0 with hl1
  set l2 : M → ℝ := fun r => if r ∈ M2 then -lam r else 0 with hl2
  have h12 : ∀ r, l1 r - l2 r = lam r := by
    intro r
    simp only [hl1, hl2]
    by_cases hr1 : r ∈ M1
    · have hr2 : r ∉ M2 := Finset.disjoint_left.1 hdisj hr1
      simp [hr1, hr2]
    · by_cases hr2 : r ∈ M2
      · simp [hr1, hr2]
      · simp [hr1, hr2, hlam_out r (by simp [hr1, hr2])]
  set L := ∑ r, lam r * btil r with hL
  set S := (∑ r, l1 r) + ∑ r, l2 r with hS
  have hsub : ∀ g : M → ℝ, ∑ r, l1 r * g r - ∑ r, l2 r * g r = ∑ r, lam r * g r := by
    intro g
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← h12 r]; ring
  have huvA : ∀ i, ∑ r, u r * Atil r i - ∑ r, v r * Atil r i =
      (if i = k then u0 else 0) + (if i = k then v0 else 0) := by
    intro i; have := h1 i; have := h2 i; linarith
  have huvb : ∑ r, u r * btil r - ∑ r, v r * btil r = v0 := by linarith
  have key := hbasis.2
    (fun i => ∑ r, (l1 r - S * u r) * Atil r i - (if i = k then -L - S * u0 else 0))
    (fun r => l1 r - S * u r) (-L - S * u0) (fun r => l2 r - S * v r) (L - S * v0)
    (∑ r, (l1 r - S * u r) * btil r)
    (by intro i; ring)
    (by
      intro i
      have e := huvA i
      have e2 := hsub (fun r => Atil r i)
      have e3 := hlamA i
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at e2 ⊢
      split_ifs at e ⊢ with hik
      · linear_combination e2 + e3 - S * e
      · linear_combination e2 + e3 - S * e)
    (by ring)
    (by
      have e2 := hsub btil
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at e2 ⊢
      linear_combination -e2 + S * huvb)
    (by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      linear_combination (-S) * h5)
    (by
      intro r hr
      simp [hl1, hr, hu_supp r hr])
    (by
      intro r hr
      simp [hl2, hr, hv_supp r hr])
  obtain ⟨-, hdu, hdu0, hdv, hdv0, -⟩ := key
  have hS0 : S = 0 := by
    have : S * (u0 + v0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  apply hy0
  funext i
  rw [← hlamι i, ← h12 (ι i)]
  have a1 := congrFun hdu (ι i)
  have a2 := congrFun hdv (ι i)
  simp only [hS0, zero_mul, sub_zero, Pi.zero_apply] at a1 a2
  simp [a1, a2]


/-- lift a vector indexed by positions to the rows. -/
def scLift {n : ℕ} {M : Type*} [DecidableEq M] (ι : Fin n → M) (z : Fin n → ℝ) : M → ℝ :=
  fun r => ∑ i, if ι i = r then z i else 0

lemma scLift_sum {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] (ι : Fin n → M)
    (z : Fin n → ℝ) (g : M → ℝ) : ∑ r, scLift ι z r * g r = ∑ i, z i * g (ι i) := by
  simp only [scLift, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

lemma scLift_apply {n : ℕ} {M : Type*} [DecidableEq M] (ι : Fin n → M)
    (hι : Function.Injective ι) (z : Fin n → ℝ) (i : Fin n) : scLift ι z (ι i) = z i := by
  simp only [scLift]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hι.ne hj]
  · simp

lemma scLift_out {n : ℕ} {M : Type*} [DecidableEq M] (ι : Fin n → M) (z : Fin n → ℝ) (r : M)
    (hr : ∀ i, ι i ≠ r) : scLift ι z r = 0 := by
  simp only [scLift]
  exact Finset.sum_eq_zero fun i _ => by simp [hr i]

lemma sc_reindex {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] (ι : Fin n → M)
    (hι : Function.Injective ι) (g : M → ℝ) (hg : ∀ r, (∀ i, ι i ≠ r) → g r = 0) :
    ∑ r, g r = ∑ i, g (ι i) := by
  have hfun : g = scLift ι (fun i => g (ι i)) := by
    funext r
    by_cases h : ∃ i, ι i = r
    · obtain ⟨i, rfl⟩ := h; rw [scLift_apply ι hι]
    · push_neg at h; rw [hg r h, scLift_out ι _ r h]
  have := scLift_sum ι (fun i => g (ι i)) (fun _ => 1)
  simp only [mul_one] at this
  rw [← this]
  exact Finset.sum_congr rfl fun r _ => by rw [← hfun]

lemma sc_inv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B.det) (w : Fin n → ℝ)
    (c : ℝ) (k : Fin n) (hw : ∀ j, ∑ i, w i * B i j = if j = k then c else 0) :
    ∀ i, w i = c * B⁻¹ k i := by
  have h1 : Matrix.vecMul w B = Pi.single k c := by
    funext j
    rw [Pi.single_apply, ← hw j]
    simp [Matrix.vecMul, dotProduct]
  have h2 : w = Matrix.vecMul (Matrix.vecMul w B) B⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]
  intro i
  rw [h2, h1]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

lemma sc_arith_core (u0 v0 a F C p q : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hpq : p = 0 ∨ q = 0) (hpa : p - q = -(u0 + v0) * a)
    (hFC : (a = F ∧ C = F) ∨ C = F + 1) :
    min (-p - u0 * F) (-q + v0 * C) =
      min ((a - F) * u0) ((1 - (a - F)) * v0) - max (a * u0) (-a * v0) := by
  rcases hpq with rfl | rfl
  · have hq' : q = (u0 + v0) * a := by linarith
    subst hq'
    have ha : 0 ≤ a := by
      by_contra h; push_neg at h; nlinarith
    rw [max_eq_left (by nlinarith), ← min_sub_sub_right]
    rcases hFC with ⟨rfl, rfl⟩ | rfl
    · rw [min_eq_left (by nlinarith), min_eq_left (by nlinarith)]; ring
    · congr 1 <;> ring
  · have hp' : p = -(u0 + v0) * a := by linarith
    subst hp'
    have ha : a ≤ 0 := by
      by_contra h; push_neg at h; nlinarith
    rw [max_eq_right (by nlinarith), ← min_sub_sub_right]
    rcases hFC with ⟨rfl, rfl⟩ | rfl
    · rw [min_eq_left (by nlinarith), min_eq_left (by nlinarith)]; ring
    · congr 1 <;> ring

lemma sc_arith_gamma (u0 v0 p q al : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hpq : p = 0 ∨ q = 0) :
    min (al - p + u0 * ⌈((al - q) - (al - p)) / (u0 + v0)⌉)
        (al - q - v0 * ⌊((al - q) - (al - p)) / (u0 + v0)⌋) - al =
      (u0 + v0) * (min (Int.fract (-(p - q) / (u0 + v0)) * (1 - v0 / (u0 + v0)))
          ((1 - Int.fract (-(p - q) / (u0 + v0))) * (v0 / (u0 + v0))) -
        max (-(p - q) / (u0 + v0) * (1 - v0 / (u0 + v0)))
          (-(-(p - q) / (u0 + v0)) * (v0 / (u0 + v0)))) := by
  have hc : 0 < u0 + v0 := by linarith
  set a := -(p - q) / (u0 + v0) with ha
  have harg : ((al - q) - (al - p)) / (u0 + v0) = -a := by rw [ha]; field_simp; ring
  rw [harg, Int.ceil_neg, Int.floor_neg]
  push_cast
  have hfr : Int.fract a = a - ⌊a⌋ := (Int.self_sub_floor a).symm
  have e1 : (u0 + v0) * (1 - v0 / (u0 + v0)) = u0 := by field_simp; ring
  have e2 : (u0 + v0) * (v0 / (u0 + v0)) = v0 := by field_simp
  rw [mul_sub, mul_min_of_nonneg _ _ hc.le, mul_max_of_nonneg _ _ hc.le]
  have r1 : (u0 + v0) * (Int.fract a * (1 - v0 / (u0 + v0))) = (a - ⌊a⌋) * u0 := by
    rw [hfr, mul_left_comm, e1]
  have r2 : (u0 + v0) * ((1 - Int.fract a) * (v0 / (u0 + v0))) = (1 - (a - ⌊a⌋)) * v0 := by
    rw [hfr, mul_left_comm, e2]
  have r3 : (u0 + v0) * (a * (1 - v0 / (u0 + v0))) = a * u0 := by rw [mul_left_comm, e1]
  have r4 : (u0 + v0) * (-a * (v0 / (u0 + v0))) = -a * v0 := by rw [mul_left_comm, e2]
  rw [r1, r2, r3, r4]
  have hpa : p - q = -(u0 + v0) * a := by rw [ha]; field_simp
  have hFC : (a = ⌊a⌋ ∧ (⌈a⌉ : ℝ) = ⌊a⌋) ∨ (⌈a⌉ : ℝ) = ⌊a⌋ + 1 := by
    rcases Int.fract_eq_zero_or_add_one_sub_ceil a with h | h
    · left
      have haF : a = ⌊a⌋ := by linarith
      refine ⟨haF, ?_⟩
      have h1 : ⌈a⌉ ≤ ⌊a⌋ := Int.ceil_le.2 (le_of_eq haF)
      have h2 : ⌊a⌋ ≤ ⌈a⌉ := Int.floor_le_ceil a
      exact_mod_cast le_antisymm h1 h2
    · right; linarith
  have := sc_arith_core u0 v0 a ⌊a⌋ ⌈a⌉ p q hu0 hv0 hp hq hpq hpa hFC
  rw [← this, ← min_sub_sub_right]
  congr 1 <;> ring

lemma sc_pi (p q u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p = 0 ∨ q = 0) :
    (u0 + v0) ^ 2 * max (-(p - q) / (u0 + v0) * (1 - v0 / (u0 + v0)))
      (-(-(p - q) / (u0 + v0)) * (v0 / (u0 + v0))) = v0 * p + u0 * q := by
  have hc : 0 < u0 + v0 := by linarith
  have e1 : -(p - q) / (u0 + v0) * (1 - v0 / (u0 + v0)) = (q - p) * u0 / (u0 + v0) ^ 2 := by
    field_simp; ring
  have e2 : -(-(p - q) / (u0 + v0)) * (v0 / (u0 + v0)) = (p - q) * v0 / (u0 + v0) ^ 2 := by
    field_simp
  rw [e1, e2, max_div_div_right (by positivity), mul_div_cancel₀ _ (by positivity)]
  rcases hpq with rfl | rfl
  · rw [max_eq_left (by nlinarith)]; ring
  · rw [max_eq_right (by nlinarith)]; ring

lemma sc_pi0 (u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) :
    (u0 + v0) ^ 2 * (v0 / (u0 + v0) * (1 - v0 / (u0 + v0))) = u0 * v0 := by
  have hc : 0 < u0 + v0 := by linarith
  field_simp; ring

/-- Part (A) core: the strengthened L&P cut of a basic solution equals the MIG cut. -/
theorem sc_A_core {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n)) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0)
    (hv0 : 0 < v0) (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hdisj : Disjoint M1 M2) (hι : Function.Injective ι)
    (himg : Finset.image ι Finset.univ = M1 ∪ M2) (hdet : IsUnit (Ahat Atil ι).det) :
    {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
      StrengthenedSimpleDisjCutSet Atil btil ι k Nprime := by
  obtain ⟨h1, h2, h3, h4, h5, hu, hv, -, -⟩ := hf
  have hc : 0 < u0 + v0 := by linarith
  have hmem : ∀ i, ι i ∈ M1 ∪ M2 := by intro i; rw [← himg]; simp
  have hout : ∀ r, (∀ i, ι i ≠ r) → r ∉ M1 ∪ M2 := by
    intro r hr hrm
    rw [← himg] at hrm
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hrm
    exact hr i hi
  have hu_out : ∀ r, (∀ i, ι i ≠ r) → u r = 0 := fun r hr =>
    hu_supp r (fun h => hout r hr (Finset.mem_union_left _ h))
  have hv_out : ∀ r, (∀ i, ι i ≠ r) → v r = 0 := fun r hr =>
    hv_supp r (fun h => hout r hr (Finset.mem_union_right _ h))
  have hpq : ∀ i, u (ι i) = 0 ∨ v (ι i) = 0 := by
    intro i
    rcases Finset.mem_union.1 (hmem i) with h | h
    · right; exact hv_supp _ (Finset.disjoint_left.1 hdisj h)
    · left; exact hu_supp _ (Finset.disjoint_right.1 hdisj h)
  have hw1 : ∀ j, ∑ i, (u (ι i) - v (ι i)) * Ahat Atil ι i j =
      if j = k then u0 + v0 else 0 := by
    intro j
    have e := sc_reindex ι hι (fun r => (u r - v r) * Atil r j)
      (by intro r hr; simp [hu_out r hr, hv_out r hr])
    simp only [Ahat]
    rw [← e]
    have e1 := h1 j
    have e2 := h2 j
    simp only [sub_mul, Finset.sum_sub_distrib]
    split_ifs at e1 e2 ⊢ <;> linarith
  have hw := sc_inv _ hdet _ (u0 + v0) k hw1
  have hwb : ∑ i, (u (ι i) - v (ι i)) * btil (ι i) = v0 := by
    have e := sc_reindex ι hι (fun r => (u r - v r) * btil r)
      (by intro r hr; simp [hu_out r hr, hv_out r hr])
    rw [← e]
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  have hA0 : Abar0 Atil btil ι k = v0 / (u0 + v0) := by
    unfold Abar0 Bhat
    simp only [Matrix.mulVec, dotProduct]
    rw [eq_div_iff hc.ne']
    conv_rhs => rw [← hwb]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw i]; ring
  have hAb : ∀ i, Abar Atil ι k i = -(u (ι i) - v (ι i)) / (u0 + v0) := by
    intro i; unfold Abar; rw [hw i]; field_simp
  have hpi : ∀ i, (u0 + v0) ^ 2 * PiCoef Atil btil ι k i = v0 * u (ι i) + u0 * v (ι i) := by
    intro i
    unfold PiCoef Pi1 Pi2
    rw [hAb i, hA0]
    exact sc_pi _ _ u0 v0 hu0 hv0 (hu (ι i)) (hv (ι i)) (hpq i)
  have hpi0 : (u0 + v0) ^ 2 * Pi0 Atil btil ι k = u0 * v0 := by
    unfold Pi0; rw [hA0]; exact sc_pi0 u0 v0 hu0 hv0
  -- affine identity for the plain cut
  have haff : ∀ x, (u0 + v0) * (dotProduct α x - β) =
      ∑ i, (v0 * u (ι i) + u0 * v (ι i)) * Surplus Atil btil ι i x - u0 * v0 := by
    intro x
    have hαu : ∀ j, α j = ∑ r, u r * Atil r j - (if j = k then u0 else 0) := by
      intro j; linarith [h1 j]
    have hαv : ∀ j, α j = ∑ r, v r * Atil r j + (if j = k then v0 else 0) := by
      intro j; linarith [h2 j]
    have hU : dotProduct α x - β = ∑ i, u (ι i) * Surplus Atil btil ι i x - u0 * x k := by
      have e : dotProduct α x = ∑ r, u r * dotProduct (Atil r) x - u0 * x k := by
        simp only [dotProduct, hαu, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [mul_assoc]
      have e2 := sc_reindex ι hι (fun r => u r * (dotProduct (Atil r) x - btil r))
        (by intro r hr; simp [hu_out r hr])
      simp only [Surplus]
      rw [e, ← e2]
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have hV : dotProduct α x - β = ∑ i, v (ι i) * Surplus Atil btil ι i x - v0 + v0 * x k := by
      have e : dotProduct α x = ∑ r, v r * dotProduct (Atil r) x + v0 * x k := by
        simp only [dotProduct, hαv, add_mul, Finset.sum_add_distrib, Finset.sum_mul, ite_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [mul_assoc]
      have e2 := sc_reindex ι hι (fun r => v r * (dotProduct (Atil r) x - btil r))
        (by intro r hr; simp [hv_out r hr])
      simp only [Surplus]
      rw [e, ← e2]
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have es : ∑ i, (v0 * u (ι i) + u0 * v (ι i)) * Surplus Atil btil ι i x =
        v0 * ∑ i, u (ι i) * Surplus Atil btil ι i x +
          u0 * ∑ i, v (ι i) * Surplus Atil btil ι i x := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [es]
    linear_combination v0 * hU + u0 * hV
  classical
  -- the strengthening, position by position
  have hD : ∀ x, ∑ i, (PiBar Atil btil ι k Nprime i - PiCoef Atil btil ι k i) *
      Surplus Atil btil ι i x = ∑ j, x j * ∑ i, (if j ∈ Nprime ∧ IsNonnegRow Atil btil (ι i) j
        then PiBar Atil btil ι k Nprime i - PiCoef Atil btil ι k i else 0) := by
    intro x
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hs : ∃ j ∈ Nprime, IsNonnegRow Atil btil (ι i) j
    · obtain ⟨j0, hj0N, hj0⟩ := hs
      have hS : Surplus Atil btil ι i x = x j0 := by
        simp [Surplus, hj0.1, hj0.2, dotProduct, Pi.single_apply]
      rw [hS, Finset.sum_eq_single j0]
      · rw [if_pos ⟨hj0N, hj0⟩]; ring
      · intro j _ hj
        rw [if_neg]
        · ring
        · rintro ⟨-, hjr⟩
          have := congrFun (hj0.1.symm.trans hjr.1) j0
          simp [Pi.single_apply, Ne.symm hj] at this
      · simp
    · have hPB : PiBar Atil btil ι k Nprime i = PiCoef Atil btil ι k i := by
        unfold PiBar; rw [if_neg hs]
      rw [hPB, sub_self, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      · ring
      · rintro ⟨hjN, hjr⟩; exact hs ⟨j, hjN, hjr⟩
  have hG : ∀ j, Gamma Atil btil u u0 v v0 Nprime α j - α j = (u0 + v0) *
      ∑ i, (if j ∈ Nprime ∧ IsNonnegRow Atil btil (ι i) j
        then PiBar Atil btil ι k Nprime i - PiCoef Atil btil ι k i else 0) := by
    intro j
    by_cases hjN : j ∈ Nprime
    swap
    · have : ∀ i, ¬ (j ∈ Nprime ∧ IsNonnegRow Atil btil (ι i) j) := fun i h => hjN h.1
      simp only [Gamma, if_neg hjN, sub_self, if_neg (this _), Finset.sum_const_zero, mul_zero]
    unfold Gamma
    rw [if_pos hjN]
    by_cases hex : ∃ i, IsNonnegRow Atil btil (ι i) j
    · obtain ⟨i0, hi0⟩ := hex
      have huniq : ∀ i, IsNonnegRow Atil btil (ι i) j → i = i0 := by
        intro i hi
        by_contra hne
        apply hdet.ne_zero
        apply Matrix.det_zero_of_row_eq hne
        funext m
        simp [Ahat, hi.1, hi0.1]
      rw [Finset.sum_eq_single i0 (fun i _ hi => by
          rw [if_neg]; rintro ⟨-, h⟩; exact hi (huniq i h)) (by simp),
        if_pos ⟨hjN, hi0⟩]
      have hjk : j ≠ k := by
        rintro rfl
        have hrow : ∀ l, (Ahat Atil ι)⁻¹ j l = if i0 = l then 1 else 0 := by
          intro l
          have := congrFun (congrFun (Matrix.mul_nonsing_inv _ hdet) i0) l
          simp only [Matrix.mul_apply, Ahat, hi0.1, Pi.single_apply, Matrix.one_apply] at this
          simpa using this
        have := hwb
        simp only [hw, hrow] at this
        simp [hi0.2] at this
        linarith
      have hA1 : Alpha1 Atil btil u j = α j - u (ι i0) := by
        unfold Alpha1
        have hr : ∀ r, (if IsNonnegRow Atil btil r j then 0 else u r * Atil r j) =
            u r * Atil r j - (if r = ι i0 then u r else 0) := by
          intro r
          by_cases hr : IsNonnegRow Atil btil r j
          · rw [if_pos hr]
            by_cases hri : r = ι i0
            · subst hri; rw [if_pos rfl, hr.1]; simp
            · rw [if_neg hri]
              have : u r = 0 := hu_out r (fun i hi => hri (by
                rw [← hi, huniq i (hi ▸ hr)]))
              simp [this]
          · rw [if_neg hr]
            have : r ≠ ι i0 := fun h => hr (h ▸ hi0)
            simp [this]
        rw [Finset.sum_congr rfl (fun r _ => hr r), Finset.sum_sub_distrib, Finset.sum_ite_eq']
        have := h1 j
        rw [if_neg hjk] at this
        simp only [Finset.mem_univ, if_true]
        linarith
      have hA2 : Alpha2 Atil btil v j = α j - v (ι i0) := by
        unfold Alpha2
        have hr : ∀ r, (if IsNonnegRow Atil btil r j then 0 else v r * Atil r j) =
            v r * Atil r j - (if r = ι i0 then v r else 0) := by
          intro r
          by_cases hr : IsNonnegRow Atil btil r j
          · rw [if_pos hr]
            by_cases hri : r = ι i0
            · subst hri; rw [if_pos rfl, hr.1]; simp
            · rw [if_neg hri]
              have : v r = 0 := hv_out r (fun i hi => hri (by
                rw [← hi, huniq i (hi ▸ hr)]))
              simp [this]
          · rw [if_neg hr]
            have : r ≠ ι i0 := fun h => hr (h ▸ hi0)
            simp [this]
        rw [Finset.sum_congr rfl (fun r _ => hr r), Finset.sum_sub_distrib, Finset.sum_ite_eq']
        have := h2 j
        rw [if_neg hjk] at this
        simp only [Finset.mem_univ, if_true]
        linarith
      have hPB : PiBar Atil btil ι k Nprime i0 =
          min (FracAbar Atil ι k i0 * (1 - Abar0 Atil btil ι k))
            ((1 - FracAbar Atil ι k i0) * Abar0 Atil btil ι k) := by
        unfold PiBar; rw [if_pos ⟨j, hjN, hi0⟩]
      rw [hPB]
      unfold MBar FracAbar PiCoef Pi1 Pi2
      rw [hA1, hA2, hAb i0, hA0]
      exact sc_arith_gamma u0 v0 _ _ (α j) hu0 hv0 (hu (ι i0)) (hv (ι i0)) (hpq i0)
    · push_neg at hex
      have hzero : ∀ i, ¬ (j ∈ Nprime ∧ IsNonnegRow Atil btil (ι i) j) := fun i h => hex i h.2
      simp only [if_neg (hzero _), Finset.sum_const_zero, mul_zero]
      have hA1 : Alpha1 Atil btil u j = ∑ r, u r * Atil r j := by
        unfold Alpha1
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hr : IsNonnegRow Atil btil r j
        · rw [if_pos hr, hu_out r (fun i hi => hex i (hi ▸ hr))]; ring
        · rw [if_neg hr]
      have hA2 : Alpha2 Atil btil v j = ∑ r, v r * Atil r j := by
        unfold Alpha2
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hr : IsNonnegRow Atil btil r j
        · rw [if_pos hr, hv_out r (fun i hi => hex i (hi ▸ hr))]; ring
        · rw [if_neg hr]
      unfold MBar
      rw [hA1, hA2]
      have e1 := h1 j
      have e2 := h2 j
      by_cases hjk : j = k
      · rw [if_pos hjk] at e1 e2
        have hm : (∑ r, v r * Atil r j - ∑ r, u r * Atil r j) / (u0 + v0) = -1 := by
          rw [div_eq_iff hc.ne']; linarith
        rw [hm]
        have hc1 : ⌈(-1 : ℝ)⌉ = -1 := by norm_num
        have hf1 : ⌊(-1 : ℝ)⌋ = -1 := by norm_num
        rw [hc1, hf1]
        push_cast
        rw [min_eq_left (by linarith)]
        linarith
      · rw [if_neg hjk] at e1 e2
        have hm : (∑ r, v r * Atil r j - ∑ r, u r * Atil r j) / (u0 + v0) = 0 := by
          rw [div_eq_iff hc.ne']; linarith
        rw [hm]
        simp only [Int.ceil_zero, Int.floor_zero, Int.cast_zero, mul_zero, add_zero, sub_zero]
        rw [min_eq_left (by linarith)]
        linarith
  have key : ∀ x, (u0 + v0) * (dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x - β) =
      (u0 + v0) ^ 2 * (∑ i, PiBar Atil btil ι k Nprime i * Surplus Atil btil ι i x -
        Pi0 Atil btil ι k) := by
    intro x
    have eG : dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x =
        dotProduct α x + ∑ j, (Gamma Atil btil u u0 v v0 Nprime α j - α j) * x j := by
      simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]; ring
    have e2 : ∑ j, (Gamma Atil btil u u0 v v0 Nprime α j - α j) * x j = (u0 + v0) *
        ∑ i, (PiBar Atil btil ι k Nprime i - PiCoef Atil btil ι k i) *
          Surplus Atil btil ι i x := by
      rw [hD x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hG j]; ring
    have e3 : ∑ i, PiBar Atil btil ι k Nprime i * Surplus Atil btil ι i x =
        ∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x +
          ∑ i, (PiBar Atil btil ι k Nprime i - PiCoef Atil btil ι k i) *
            Surplus Atil btil ι i x := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e4 : (u0 + v0) ^ 2 * ∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x =
        ∑ i, (v0 * u (ι i) + u0 * v (ι i)) * Surplus Atil btil ι i x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hpi i]; ring
    rw [eG, e2, e3]
    linear_combination haff x - e4 + hpi0
  ext x
  simp only [Set.mem_setOf_eq, StrengthenedSimpleDisjCutSet]
  have hc2 : 0 < (u0 + v0) ^ 2 := by positivity
  constructor
  · intro h
    have h' : 0 ≤ (u0 + v0) ^ 2 * (∑ i, PiBar Atil btil ι k Nprime i *
        Surplus Atil btil ι i x - Pi0 Atil btil ι k) := by
      rw [← key x]; exact mul_nonneg hc.le (by linarith)
    have := (mul_nonneg_iff_of_pos_left hc2).1 h'
    linarith
  · intro h
    have h' : 0 ≤ (u0 + v0) * (dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x - β) := by
      rw [key x]; exact mul_nonneg hc2.le (by linarith)
    have := (mul_nonneg_iff_of_pos_left hc).1 h'
    linarith

/-- A feasible point supported on a basis is an extreme point. -/
lemma sc_extreme {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (k : Fin n) (M1 M2 : Finset M) (hbasis : IsCGLPKBasis Atil btil k M1 M2)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ)
    (hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0) :
    IsBasicCGLPKSolution Atil btil k α u u0 v v0 β := by
  have uniq : ∀ y ∈ CGLPKFeasibleSet Atil btil k, (∀ ρ ∉ M1, y.2.1 ρ = 0) →
      (∀ ρ ∉ M2, y.2.2.2.1 ρ = 0) → y = (α, u, u0, v, v0, β) := by
    rintro ⟨yα, yu, yu0, yv, yv0, yβ⟩ hy hyu hyv
    simp only [CGLPKFeasibleSet, Set.mem_setOf_eq] at hy
    obtain ⟨g1, g2, g3, g4, g5, -, -, -, -⟩ := hy
    obtain ⟨h1, h2, h3, h4, h5, -, -, -, -⟩ := hf
    have key := hbasis.2 (yα - α) (yu - u) (yu0 - u0) (yv - v) (yv0 - v0) (yβ - β)
      (by
        intro i
        have a := g1 i; have b := h1 i
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        split_ifs at a b ⊢ <;> linarith)
      (by
        intro i
        have a := g2 i; have b := h2 i
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        split_ifs at a b ⊢ <;> linarith)
      (by simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; linarith)
      (by simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; linarith)
      (by simp only [Pi.sub_apply, Finset.sum_sub_distrib]; linarith)
      (by intro ρ hρ; have := hyu ρ hρ; simp only at this; simp [this, hu_supp ρ hρ])
      (by intro ρ hρ; have := hyv ρ hρ; simp only at this; simp [this, hv_supp ρ hρ])
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := key
    simp only [Prod.mk.injEq]
    refine ⟨sub_eq_zero.1 k1, sub_eq_zero.1 k2, sub_eq_zero.1 k3, sub_eq_zero.1 k4,
      sub_eq_zero.1 k5, sub_eq_zero.1 k6⟩
  refine ⟨hf, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, hyz⟩ := hseg
  have hy' := hy
  have hz' := hz
  simp only [CGLPKFeasibleSet, Set.mem_setOf_eq] at hy' hz'
  apply uniq y hy
  · intro ρ hρ
    have e := congrArg (fun p => p.2.1 ρ) hyz
    simp only [Prod.smul_snd, Prod.snd_add, Prod.smul_fst, Prod.fst_add, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at e
    rw [hu_supp ρ hρ] at e
    have p1 := hy'.2.2.2.2.2.1 ρ
    have p2 := hz'.2.2.2.2.2.1 ρ
    simp only [Pi.zero_apply] at p1 p2
    nlinarith [mul_nonneg ha.le p1, mul_nonneg hb.le p2]
  · intro ρ hρ
    have e := congrArg (fun p => p.2.2.2.1 ρ) hyz
    simp only [Prod.smul_snd, Prod.snd_add, Prod.smul_fst, Prod.fst_add, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at e
    rw [hv_supp ρ hρ] at e
    have p1 := hy'.2.2.2.2.2.2.1 ρ
    have p2 := hz'.2.2.2.2.2.2.1 ρ
    simp only [Pi.zero_apply] at p1 p2
    nlinarith [mul_nonneg ha.le p1, mul_nonneg hb.le p2]

/-- Part (B) core: construction of the basic solution from a basis. -/
theorem sc_B_core {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n)) (k : Fin n)
    (ι : Fin n → M) (M1 M2 : Finset M) (hι : Function.Injective ι)
    (hdet : IsUnit (Ahat Atil ι).det) (h0 : 0 < Abar0 Atil btil ι k)
    (h1' : Abar0 Atil btil ι k < 1) (hdisj : Disjoint M1 M2)
    (himg : M1 ∪ M2 = Finset.image ι Finset.univ)
    (hsign : ∀ i, (Pi1 Atil btil ι k i < Pi2 Atil btil ι k i → ι i ∈ M1) ∧
        (Pi2 Atil btil ι k i < Pi1 Atil btil ι k i → ι i ∈ M2)) :
    ∃ (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ),
        IsBasicCGLPKSolution Atil btil k α u u0 v v0 β ∧ 0 < u0 ∧ 0 < v0 ∧
        (∀ ρ ∉ M1, u ρ = 0) ∧ (∀ ρ ∉ M2, v ρ = 0) ∧ IsCGLPKBasis Atil btil k M1 M2 ∧
        {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
          StrengthenedSimpleDisjCutSet Atil btil ι k Nprime := by
  set f0 := Abar0 Atil btil ι k with hf0
  set a : Fin n → ℝ := fun i => Abar Atil ι k i with ha_def
  have ha_inv : ∀ i, a i = -(Ahat Atil ι)⁻¹ k i := fun i => rfl
  have hmem : ∀ i, ι i ∈ M1 ∪ M2 := by intro i; rw [himg]; simp
  have hout : ∀ r, (∀ i, ι i ≠ r) → r ∉ M1 ∪ M2 := by
    intro r hr hrm
    rw [himg] at hrm
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hrm
    exact hr i hi
  have hM1 : ∀ i, ι i ∈ M1 → a i ≤ 0 := by
    intro i hi
    have hn2 : ι i ∉ M2 := Finset.disjoint_left.1 hdisj hi
    have := mt (hsign i).2 hn2
    push_neg at this
    simp only [Pi1, Pi2] at this
    rw [ha_def]
    nlinarith
  have hM2 : ∀ i, ι i ∈ M2 → 0 ≤ a i := by
    intro i hi
    have hn1 : ι i ∉ M1 := Finset.disjoint_right.1 hdisj hi
    have := mt (hsign i).1 hn1
    push_neg at this
    simp only [Pi1, Pi2] at this
    rw [ha_def]
    nlinarith
  set T : ℝ := 1 + ∑ i, |a i| with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  set t : ℝ := 1 / T with ht
  have htpos : 0 < t := by positivity
  set zU : Fin n → ℝ := fun i => if ι i ∈ M1 then -t * a i else 0 with hzU
  set zV : Fin n → ℝ := fun i => if ι i ∈ M2 then t * a i else 0 with hzV
  set u : M → ℝ := scLift ι zU with hu
  set v : M → ℝ := scLift ι zV with hv
  set u0 : ℝ := t * (1 - f0) with hu0
  set v0 : ℝ := t * f0 with hv0
  set α : Fin n → ℝ := fun j => ∑ r, u r * Atil r j - (if j = k then u0 else 0) with hα
  set β : ℝ := ∑ r, u r * btil r with hβ
  have hu0pos : 0 < u0 := mul_pos htpos (by linarith)
  have hv0pos : 0 < v0 := mul_pos htpos h0
  have hzU_nn : ∀ i, 0 ≤ zU i := by
    intro i; simp only [hzU]; split_ifs with h
    · have := hM1 i h; nlinarith
    · exact le_rfl
  have hzV_nn : ∀ i, 0 ≤ zV i := by
    intro i; simp only [hzV]; split_ifs with h
    · have := hM2 i h; positivity
    · exact le_rfl
  have hdiff : ∀ i, zU i - zV i = t * (Ahat Atil ι)⁻¹ k i := by
    intro i
    simp only [hzU, hzV]
    rcases Finset.mem_union.1 (hmem i) with h | h
    · have h2 : ι i ∉ M2 := Finset.disjoint_left.1 hdisj h
      rw [if_pos h, if_neg h2, ha_inv]; ring
    · have h1 : ι i ∉ M1 := Finset.disjoint_right.1 hdisj h
      rw [if_neg h1, if_pos h, ha_inv]; ring
  have hsumabs : ∀ i, zU i + zV i = t * |a i| := by
    intro i
    simp only [hzU, hzV]
    rcases Finset.mem_union.1 (hmem i) with h | h
    · have h2 : ι i ∉ M2 := Finset.disjoint_left.1 hdisj h
      rw [if_pos h, if_neg h2, abs_of_nonpos (hM1 i h)]; ring
    · have h1 : ι i ∉ M1 := Finset.disjoint_right.1 hdisj h
      rw [if_neg h1, if_pos h, abs_of_nonneg (hM2 i h)]; ring
  have hinvA : ∀ j, ∑ i, (Ahat Atil ι)⁻¹ k i * Atil (ι i) j = if j = k then 1 else 0 := by
    intro j
    have := congrFun (congrFun (Matrix.nonsing_inv_mul _ hdet) k) j
    simp only [Matrix.mul_apply, Ahat, Matrix.one_apply] at this
    rw [this]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk, Ne.symm hjk]
  have hinvb : ∑ i, (Ahat Atil ι)⁻¹ k i * btil (ι i) = f0 := by
    simp [hf0, Abar0, Matrix.mulVec, dotProduct, Bhat]
  have hu_supp : ∀ ρ ∉ M1, u ρ = 0 := by
    intro ρ hρ
    simp only [hu, scLift]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · simp only [hzU]; rw [if_neg (h ▸ hρ)]
    · rfl
  have hv_supp : ∀ ρ ∉ M2, v ρ = 0 := by
    intro ρ hρ
    simp only [hv, scLift]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · simp only [hzV]; rw [if_neg (h ▸ hρ)]
    · rfl
  have hfeas : IsCGLPKFeasible Atil btil k α u u0 v v0 β := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hu0pos.le, hv0pos.le⟩
    · intro i; simp only [hα]; ring
    · intro j
      simp only [hα]
      have e1 := scLift_sum ι zU (fun r => Atil r j)
      have e2 := scLift_sum ι zV (fun r => Atil r j)
      simp only [← hu, ← hv] at e1 e2
      rw [e1, e2]
      have e3 : ∑ i, zU i * Atil (ι i) j - ∑ i, zV i * Atil (ι i) j =
          t * ∑ i, (Ahat Atil ι)⁻¹ k i * Atil (ι i) j := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [← sub_mul, hdiff i]; ring
      rw [hinvA j] at e3
      split_ifs at e3 ⊢ with hjk
      · simp only [hu0, hv0]; linear_combination e3
      · linear_combination e3
    · simp only [hβ]; ring
    · simp only [hβ]
      have e1 := scLift_sum ι zU btil
      have e2 := scLift_sum ι zV btil
      simp only [← hu, ← hv] at e1 e2
      rw [e1, e2]
      have e3 : ∑ i, zU i * btil (ι i) - ∑ i, zV i * btil (ι i) =
          t * ∑ i, (Ahat Atil ι)⁻¹ k i * btil (ι i) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [← sub_mul, hdiff i]; ring
      rw [hinvb] at e3
      simp only [hv0]
      linear_combination -e3
    · have e1 := scLift_sum ι zU (fun _ => 1)
      have e2 := scLift_sum ι zV (fun _ => 1)
      simp only [mul_one, ← hu, ← hv] at e1 e2
      rw [e1, e2]
      have hz : ∑ i, zU i + ∑ i, zV i = t * ∑ i, |a i| := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => hsumabs i
      have : t * T = 1 := by rw [ht]; field_simp
      rw [hT] at this
      simp only [hu0, hv0]
      linear_combination hz + this
    · intro r
      simp only [hu, scLift, Pi.zero_apply]
      exact Finset.sum_nonneg fun i _ => by split_ifs; exacts [hzU_nn i, le_rfl]
    · intro r
      simp only [hv, scLift, Pi.zero_apply]
      exact Finset.sum_nonneg fun i _ => by split_ifs; exacts [hzV_nn i, le_rfl]
  have hbasis : IsCGLPKBasis Atil btil k M1 M2 := by
    refine ⟨?_, ?_⟩
    · rw [← Finset.card_union_of_disjoint hdisj, himg, Finset.card_image_of_injective _ hι]
      simp
    intro dα du du0 dv dv0 dβ e1 e2 e3 e4 e5 s1 s2
    have du_out : ∀ r, (∀ i, ι i ≠ r) → du r = 0 := fun r hr =>
      s1 r (fun h => hout r hr (Finset.mem_union_left _ h))
    have dv_out : ∀ r, (∀ i, ι i ≠ r) → dv r = 0 := fun r hr =>
      s2 r (fun h => hout r hr (Finset.mem_union_right _ h))
    have hw1 : ∀ j, ∑ i, (du (ι i) - dv (ι i)) * Ahat Atil ι i j =
        if j = k then du0 + dv0 else 0 := by
      intro j
      have e := sc_reindex ι hι (fun r => (du r - dv r) * Atil r j)
        (by intro r hr; simp [du_out r hr, dv_out r hr])
      simp only [Ahat]
      rw [← e]
      have a1 := e1 j
      have a2 := e2 j
      simp only [sub_mul, Finset.sum_sub_distrib]
      split_ifs at a1 a2 ⊢ <;> linarith
    have hw := sc_inv _ hdet _ (du0 + dv0) k hw1
    have hwb : ∑ i, (du (ι i) - dv (ι i)) * btil (ι i) = dv0 := by
      have e := sc_reindex ι hι (fun r => (du r - dv r) * btil r)
        (by intro r hr; simp [du_out r hr, dv_out r hr])
      rw [← e]
      simp only [sub_mul, Finset.sum_sub_distrib]
      linarith
    have hdv0 : dv0 = (du0 + dv0) * f0 := by
      have : (du0 + dv0) * f0 = ∑ i, (du (ι i) - dv (ι i)) * btil (ι i) := by
        rw [← hinvb, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
      linarith
    have hpm : ∀ i, du (ι i) + dv (ι i) = (du0 + dv0) * |a i| := by
      intro i
      rcases Finset.mem_union.1 (hmem i) with h | h
      · have h2 : ι i ∉ M2 := Finset.disjoint_left.1 hdisj h
        have := hw i
        rw [s2 _ h2] at this ⊢
        rw [abs_of_nonpos (hM1 i h), ha_inv]; linarith
      · have h1 : ι i ∉ M1 := Finset.disjoint_right.1 hdisj h
        have := hw i
        rw [s1 _ h1] at this ⊢
        rw [abs_of_nonneg (hM2 i h), ha_inv]; linarith
    have hsum : (∑ r, du r) + ∑ r, dv r = (du0 + dv0) * ∑ i, |a i| := by
      rw [sc_reindex ι hι du du_out, sc_reindex ι hι dv dv_out, ← Finset.sum_add_distrib,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hpm i
    have hs : du0 + dv0 = 0 := by
      have : (du0 + dv0) * T = 0 := by rw [hT]; linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
    have hdv0' : dv0 = 0 := by rw [hdv0, hs, zero_mul]
    have hdu0' : du0 = 0 := by linarith
    have hdu : du = 0 := by
      funext r
      by_cases hr : ∃ i, ι i = r
      · obtain ⟨i, rfl⟩ := hr
        have := hw i
        rw [hs, zero_mul] at this
        rcases Finset.mem_union.1 (hmem i) with h | h
        · have h2 : ι i ∉ M2 := Finset.disjoint_left.1 hdisj h
          rw [s2 _ h2] at this; simpa using this
        · have h1 : ι i ∉ M1 := Finset.disjoint_right.1 hdisj h
          exact s1 _ h1
      · push_neg at hr; exact du_out r hr
    have hdv : dv = 0 := by
      funext r
      by_cases hr : ∃ i, ι i = r
      · obtain ⟨i, rfl⟩ := hr
        have := hw i
        rw [hs, zero_mul] at this
        rcases Finset.mem_union.1 (hmem i) with h | h
        · have h2 : ι i ∉ M2 := Finset.disjoint_left.1 hdisj h
          exact s2 _ h2
        · have h1 : ι i ∉ M1 := Finset.disjoint_right.1 hdisj h
          rw [s1 _ h1] at this; simp only [Pi.zero_apply]; linarith
      · push_neg at hr; exact dv_out r hr
    refine ⟨?_, hdu, hdu0', hdv, hdv0', ?_⟩
    · funext i
      have := e1 i
      simp only [hdu, hdu0', Pi.zero_apply, zero_mul, Finset.sum_const_zero, ite_self,
        add_zero, sub_zero] at this
      simpa using this
    · have := e3
      simp only [hdu, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at this
      linarith
  refine ⟨α, u, u0, v, v0, β, sc_extreme Atil btil k M1 M2 hbasis α u u0 v v0 β hfeas
    hu_supp hv_supp, hu0pos, hv0pos, hu_supp, hv_supp, hbasis, ?_⟩
  exact sc_A_core Atil btil Nprime k α u u0 v v0 β M1 M2 ι hfeas hu0pos hv0pos hu_supp hv_supp
    hdisj hι himg.symm hdet

theorem scc_core {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [inst : DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem Atil btil Nprime) (k : Fin n) :
    (∀ (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
        (ι : Fin n → M),
      IsBasicCGLPKSolution Atil btil k α u u0 v v0 β → 0 < u0 → 0 < v0 →
      (∀ ρ ∉ M1, u ρ = 0) → (∀ ρ ∉ M2, v ρ = 0) → IsCGLPKBasis Atil btil k M1 M2 →
      Function.Injective ι → Finset.image ι Finset.univ = M1 ∪ M2 →
      {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
        StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) ∧
    (∀ (ι : Fin n → M) (M1 M2 : Finset M),
      Function.Injective ι → IsUnit (Ahat Atil ι).det →
      0 < Abar0 Atil btil ι k → Abar0 Atil btil ι k < 1 →
      Disjoint M1 M2 → M1 ∪ M2 = Finset.image ι Finset.univ →
      (∀ i, (Pi1 Atil btil ι k i < Pi2 Atil btil ι k i → ι i ∈ M1) ∧
        (Pi2 Atil btil ι k i < Pi1 Atil btil ι k i → ι i ∈ M2)) →
      ∃ (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ),
        IsBasicCGLPKSolution Atil btil k α u u0 v v0 β ∧ 0 < u0 ∧ 0 < v0 ∧
        (∀ ρ ∉ M1, u ρ = 0) ∧ (∀ ρ ∉ M2, v ρ = 0) ∧ IsCGLPKBasis Atil btil k M1 M2 ∧
        {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
          StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) := by
  have hinst : inst = instDecidableEqFin n := Subsingleton.elim _ _
  subst hinst
  refine ⟨?_, ?_⟩
  · intro α u u0 v v0 β M1 M2 ι hbasic hu0 hv0 hu_supp hv_supp hbasis hι himg
    have hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β := hbasic.1
    have hdisj := bc_disjoint Atil btil k α u u0 v v0 β M1 M2 hf hu0 hu_supp hv_supp hbasis
    have hmem : ∀ i, ι i ∈ M1 ∪ M2 := by intro i; rw [← himg]; simp
    have hdet := bc_det Atil btil k α u u0 v v0 β M1 M2 hf hu0 hv0 hu_supp hv_supp hbasis
      hdisj ι hι hmem
    exact sc_A_core Atil btil Nprime k α u u0 v v0 β M1 M2 ι hf hu0 hv0 hu_supp hv_supp hdisj
      hι himg hdet
  · intro ι M1 M2 hι hdet h0 h1 hdisj himg hsign
    exact sc_B_core Atil btil Nprime k ι M1 M2 hι hdet h0 h1 hdisj himg hsign

end Disjunctive.CutCorrespondence

open Disjunctive.CutCorrespondence


theorem solution {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem Atil btil Nprime) (k : Fin n) :
    (∀ (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
        (ι : Fin n → M),
      IsBasicCGLPKSolution Atil btil k α u u0 v v0 β → 0 < u0 → 0 < v0 →
      (∀ ρ ∉ M1, u ρ = 0) → (∀ ρ ∉ M2, v ρ = 0) → IsCGLPKBasis Atil btil k M1 M2 →
      Function.Injective ι → Finset.image ι Finset.univ = M1 ∪ M2 →
      {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
        StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) ∧
    (∀ (ι : Fin n → M) (M1 M2 : Finset M),
      Function.Injective ι → IsUnit (Ahat Atil ι).det →
      0 < Abar0 Atil btil ι k → Abar0 Atil btil ι k < 1 →
      Disjoint M1 M2 → M1 ∪ M2 = Finset.image ι Finset.univ →
      (∀ i, (Pi1 Atil btil ι k i < Pi2 Atil btil ι k i → ι i ∈ M1) ∧
        (Pi2 Atil btil ι k i < Pi1 Atil btil ι k i → ι i ∈ M2)) →
      ∃ (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ),
        IsBasicCGLPKSolution Atil btil k α u u0 v v0 β ∧ 0 < u0 ∧ 0 < v0 ∧
        (∀ ρ ∉ M1, u ρ = 0) ∧ (∀ ρ ∉ M2, v ρ = 0) ∧ IsCGLPKBasis Atil btil k M1 M2 ∧
        {x | β ≤ dotProduct (Gamma Atil btil u u0 v v0 Nprime α) x} =
          StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) := by
  exact scc_core Atil btil Nprime hsys k
