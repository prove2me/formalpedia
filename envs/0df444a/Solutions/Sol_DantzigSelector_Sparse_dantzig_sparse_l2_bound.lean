-- Prove2me | solution 1 for DantzigSelector.Sparse.dantzig_sparse_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:24:06.665565+00:00
-- url     : https://prove2.me/submissions/57c68958-1b4e-4c09-b2f7-5d6cf07cd030

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model

set_option autoImplicit false

open CandesTao.Decoding DantzigSelector.Sparse MeasureTheory ProbabilityTheory

namespace DS6

/-- correlation vector `Xᵀ X v`. -/
noncomputable def corr {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) : Fin p → ℝ :=
  X.transpose.mulVec (X.mulVec v)

lemma corr_apply {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) (j : Fin p) :
    corr X v j = ∑ i, (X.mulVec v) i * X i j := by
  unfold corr
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma sum_mul_corr {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (w v : Fin p → ℝ) :
    ∑ j, w j * corr X v j = (X.mulVec w) ⬝ᵥ (X.mulVec v) := by
  change w ⬝ᵥ corr X v = _
  rw [corr, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma l2Norm_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ l2Norm x := Real.sqrt_nonneg _

lemma l2Norm_sq {m : ℕ} (x : Fin m → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma l2Norm_sq_dot {m : ℕ} (x : Fin m → ℝ) : l2Norm x ^ 2 = x ⬝ᵥ x := by
  rw [l2Norm_sq]; simp [dotProduct, sq]

lemma abs_dot_le {m : ℕ} (x y : Fin m → ℝ) : |x ⬝ᵥ y| ≤ l2Norm x * l2Norm y := by
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -x i) y
  simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at h2
  rw [abs_le]
  unfold l2Norm
  simp only [dotProduct]
  constructor <;> linarith

lemma l2Norm_ite {m : ℕ} (E : Finset (Fin m)) (f : Fin m → ℝ) :
    l2Norm (fun j => if j ∈ E then f j else 0) = √(∑ j ∈ E, f j ^ 2) := by
  unfold l2Norm
  congr 1
  simp [ite_pow, Finset.sum_ite_mem]

lemma abs_le_l1Norm {m : ℕ} (x : Fin m → ℝ) (j : Fin m) : |x j| ≤ l1Norm x :=
  Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

lemma frob {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) :
    l2Norm (X.mulVec v) ^ 2 ≤ (∑ i, ∑ j, X i j ^ 2) * l2Norm v ^ 2 := by
  rw [l2Norm_sq, l2Norm_sq, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => by
    simpa [Matrix.mulVec, dotProduct] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) v

lemma frob_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ ∑ i, ∑ j, X i j ^ 2 :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma norm_mulVec_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) :
    l2Norm (X.mulVec v) ≤ √(∑ i, ∑ j, X i j ^ 2) * l2Norm v := by
  have := Real.sqrt_le_sqrt (frob X v)
  rwa [Real.sqrt_mul (frob_nonneg X), Real.sqrt_sq (l2Norm_nonneg _),
    Real.sqrt_sq (l2Norm_nonneg _)] at this

lemma le_sInf_mul {A : Set ℝ} (hA : A.Nonempty) {q t : ℝ} (hq : 0 ≤ q)
    (h : ∀ s ∈ A, t ≤ s * q) : t ≤ sInf A * q := by
  rcases hq.eq_or_lt with hq0 | hq0
  · obtain ⟨s, hs⟩ := hA
    have := h s hs
    rw [← hq0] at this ⊢
    simpa using this
  · have : t / q ≤ sInf A := le_csInf hA fun s hs => by rw [div_le_iff₀ hq0]; exact h s hs
    rwa [div_le_iff₀ hq0] at this

lemma rip_aux (A : Set ℝ) (hA : A.Nonempty) (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ s ∈ A, (1 - s) * a ≤ b) : (1 - sInf A) * a ≤ b := by
  have := le_sInf_mul hA ha (t := a - b) fun s hs => by have := h s hs; linarith
  linarith

lemma rip_lower {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (U : Finset (Fin p))
    (hU : U.card ≤ k) (v : Fin p → ℝ) (hv : SupportedOn v U) :
    (1 - restrictedIsometryConst X k) * l2Norm v ^ 2 ≤ l2Norm (X.mulVec v) ^ 2 := by
  have hM := frob_nonneg X
  unfold restrictedIsometryConst
  apply rip_aux
  · refine ⟨∑ i, ∑ j, X i j ^ 2 + 1, by linarith, fun T _ c _ => ⟨?_, ?_⟩⟩
    · have := sq_nonneg (l2Norm c); have := sq_nonneg (l2Norm (X.mulVec c)); nlinarith
    · have := frob X c; have := sq_nonneg (l2Norm c); nlinarith
  · exact sq_nonneg _
  · intro s hs
    exact (hs.2 U hU v hv).1

lemma rop_bound {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k k' : ℕ) (U U' : Finset (Fin p))
    (hd : Disjoint U U') (hU : U.card ≤ k) (hU' : U'.card ≤ k') (v v' : Fin p → ℝ)
    (hv : SupportedOn v U) (hv' : SupportedOn v' U') :
    |(X.mulVec v) ⬝ᵥ (X.mulVec v')| ≤ restrictedOrthogonalityConst X k k' * l2Norm v * l2Norm v' := by
  have hM := frob_nonneg X
  rw [mul_assoc]
  unfold restrictedOrthogonalityConst
  refine le_sInf_mul ?_ (mul_nonneg (l2Norm_nonneg _) (l2Norm_nonneg _)) ?_
  · refine ⟨∑ i, ∑ j, X i j ^ 2, hM, fun T T' _ _ _ c c' _ _ => ?_⟩
    calc |(X.mulVec c) ⬝ᵥ (X.mulVec c')| ≤ l2Norm (X.mulVec c) * l2Norm (X.mulVec c') :=
          abs_dot_le _ _
      _ ≤ (√(∑ i, ∑ j, X i j ^ 2) * l2Norm c) * (√(∑ i, ∑ j, X i j ^ 2) * l2Norm c') :=
          mul_le_mul (norm_mulVec_le X c) (norm_mulVec_le X c') (l2Norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (l2Norm_nonneg _))
      _ = (√(∑ i, ∑ j, X i j ^ 2) * √(∑ i, ∑ j, X i j ^ 2)) * l2Norm c * l2Norm c' := by ring
      _ = (∑ i, ∑ j, X i j ^ 2) * l2Norm c * l2Norm c' := by rw [Real.mul_self_sqrt hM]
  · intro s hs
    have := hs.2 U U' hd hU hU' v v' hv hv'
    rwa [mul_assoc] at this

lemma ric_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    0 ≤ restrictedIsometryConst X k :=
  Real.sInf_nonneg fun _ hx => hx.1

lemma roc_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k k' : ℕ) :
    0 ≤ restrictedOrthogonalityConst X k k' :=
  Real.sInf_nonneg fun _ hx => hx.1

/-! ### restriction and blocks -/

def rs {p : ℕ} (h : Fin p → ℝ) (T : Finset (Fin p)) : Fin p → ℝ :=
  fun j => if j ∈ T then h j else 0

lemma rs_supp {p : ℕ} (h : Fin p → ℝ) (T : Finset (Fin p)) : SupportedOn (rs h T) T :=
  fun j hj => by simp [rs, hj]

lemma l2Norm_rs {p : ℕ} (h : Fin p → ℝ) (T : Finset (Fin p)) : l2Norm (rs h T) = l2On h T := by
  unfold rs; rw [l2Norm_ite]; rfl

lemma rs_split {p : ℕ} (h : Fin p → ℝ) (U R : Finset (Fin p)) (hd : Disjoint U R) :
    rs h (U ∪ R) = rs h U + rs h R := by
  funext j
  simp only [rs, Pi.add_apply, Finset.mem_union]
  by_cases hU : j ∈ U <;> by_cases hR : j ∈ R
  · exact absurd hR (Finset.disjoint_left.1 hd hU)
  all_goals simp [hU, hR]

lemma l1On_nonneg {p : ℕ} (h : Fin p → ℝ) (T : Finset (Fin p)) : 0 ≤ l1On h T :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l2On_nonneg {p : ℕ} (h : Fin p → ℝ) (T : Finset (Fin p)) : 0 ≤ l2On h T :=
  Real.sqrt_nonneg _

lemma l2On_le_card {p : ℕ} (h : Fin p → ℝ) (R : Finset (Fin p)) (t : ℝ) (ht : 0 ≤ t)
    (hR : ∀ k ∈ R, |h k| ≤ t) : l2On h R ≤ √(R.card : ℝ) * t := by
  unfold l2On
  have h1 : ∑ j ∈ R, h j ^ 2 ≤ ∑ j ∈ R, t ^ 2 := Finset.sum_le_sum fun k hk => by
    have := hR k hk; have := abs_nonneg (h k); have := sq_abs (h k); nlinarith
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  calc √(∑ j ∈ R, h j ^ 2) ≤ √((R.card : ℝ) * t ^ 2) := Real.sqrt_le_sqrt h1
    _ = √(R.card : ℝ) * t := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]

lemma top_exists {M : ℕ} (δ : Fin M → ℝ) (S : Finset (Fin M)) (m : ℕ) (hm : m ≤ S.card) :
    ∃ J1 ⊆ S, J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ S \ J1, |δ k| ≤ |δ j| := by
  classical
  induction m with
  | zero => exact ⟨∅, Finset.empty_subset _, Finset.card_empty, by simp⟩
  | succ m ih =>
    obtain ⟨J1, hsub, hcard, hprop⟩ := ih (by omega)
    have hne : (S \ J1).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]; omega
    obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image (S \ J1) (fun k => |δ k|) hne
    have hk0S : k0 ∈ S := (Finset.mem_sdiff.mp hk0).1
    have hk0J : k0 ∉ J1 := (Finset.mem_sdiff.mp hk0).2
    refine ⟨insert k0 J1, Finset.insert_subset hk0S hsub, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hk0J, hcard]
    · intro j hj k hk
      have hkS : k ∈ S := (Finset.mem_sdiff.mp hk).1
      have hkI : k ∉ insert k0 J1 := (Finset.mem_sdiff.mp hk).2
      have hkJ : k ∉ J1 := fun h => hkI (Finset.mem_insert_of_mem h)
      have hkSJ : k ∈ S \ J1 := Finset.mem_sdiff.mpr ⟨hkS, hkJ⟩
      rcases Finset.mem_insert.mp hj with rfl | hjJ
      · exact hmax k hkSJ
      · exact hprop j hjJ k hkSJ

lemma tail_bound {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M)) (m : ℕ) (hm : 0 < m)
    (hT : IsTopBlock δ J0 J1 m) :
    ∑ k ∈ (J0 ∪ J1)ᶜ, δ k ^ 2 ≤ (l1On δ J0ᶜ) ^ 2 / m := by
  classical
  obtain ⟨hsub, hcard, hprop⟩ := hT
  set b := l1On δ J0ᶜ with hb
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hJ1b : ∑ j ∈ J1, |δ j| ≤ b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  have hpt : ∀ k ∈ (J0 ∪ J1)ᶜ, |δ k| ≤ b / m := by
    intro k hk
    have hk' : k ∈ J0ᶜ \ J1 := by
      simp only [Finset.mem_compl, Finset.mem_union, not_or] at hk
      simp [hk.1, hk.2]
    have : ∑ j ∈ J1, |δ k| ≤ ∑ j ∈ J1, |δ j| :=
      Finset.sum_le_sum (fun j hj => hprop j hj k hk')
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    rw [le_div_iff₀ hmR]; linarith
  have hsubc : (J0 ∪ J1)ᶜ ⊆ J0ᶜ := Finset.compl_subset_compl.mpr Finset.subset_union_left
  have hrest : ∑ k ∈ (J0 ∪ J1)ᶜ, |δ k| ≤ b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubc (fun _ _ _ => abs_nonneg _)
  have hb0 : 0 ≤ b := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc ∑ k ∈ (J0 ∪ J1)ᶜ, δ k ^ 2 = ∑ k ∈ (J0 ∪ J1)ᶜ, |δ k| * |δ k| := by
        apply Finset.sum_congr rfl; intro k _; rw [abs_mul_abs_self, sq]
    _ ≤ ∑ k ∈ (J0 ∪ J1)ᶜ, b / m * |δ k| :=
        Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hpt k hk) (abs_nonneg _))
    _ = b / m * ∑ k ∈ (J0 ∪ J1)ᶜ, |δ k| := by rw [Finset.mul_sum]
    _ ≤ b / m * b := mul_le_mul_of_nonneg_left hrest (by positivity)
    _ = b ^ 2 / m := by ring

lemma sqrt_avg (S : ℕ) (hS : 1 ≤ S) (L : ℝ) : √(S : ℝ) * (L / S) = L / √(S : ℝ) := by
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hsp : 0 < √(S : ℝ) := Real.sqrt_pos.2 hSpos
  have hs : √(S : ℝ) * √(S : ℝ) = S := Real.mul_self_sqrt hSpos.le
  rw [eq_div_iff hsp.ne']
  calc √(S : ℝ) * (L / S) * √(S : ℝ) = L * (√(S : ℝ) * √(S : ℝ)) / S := by ring
    _ = L := by rw [hs]; field_simp

/-- the shelling bound: blocks of size `S` in decreasing order. -/
lemma shell {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S) (θ : ℝ) (hθ : 0 ≤ θ)
    (U : Finset (Fin p)) (v : Fin p → ℝ)
    (hrop : ∀ (U' : Finset (Fin p)) (v' : Fin p → ℝ), Disjoint U U' → U'.card ≤ S →
      SupportedOn v' U' → |(X.mulVec v) ⬝ᵥ (X.mulVec v')| ≤ θ * l2Norm v * l2Norm v')
    (h : Fin p → ℝ) :
    ∀ (N : ℕ) (R : Finset (Fin p)), R.card ≤ N → Disjoint U R → ∀ t : ℝ, 0 ≤ t →
      (∀ k ∈ R, |h k| ≤ t) →
      |(X.mulVec v) ⬝ᵥ (X.mulVec (rs h R))| ≤
        θ * l2Norm v * (√(S : ℝ) * t + l1On h R / √(S : ℝ)) := by
  classical
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hK : 0 ≤ θ * l2Norm v := mul_nonneg hθ (l2Norm_nonneg _)
  have base : ∀ R : Finset (Fin p), R.card ≤ S → Disjoint U R → ∀ t : ℝ, 0 ≤ t →
      (∀ k ∈ R, |h k| ≤ t) →
      |(X.mulVec v) ⬝ᵥ (X.mulVec (rs h R))| ≤
        θ * l2Norm v * (√(S : ℝ) * t + l1On h R / √(S : ℝ)) := by
    intro R hc hd t ht hR
    have h1 := hrop R (rs h R) hd hc (rs_supp h R)
    rw [l2Norm_rs] at h1
    have h2 := l2On_le_card h R t ht hR
    have h3 : √(R.card : ℝ) ≤ √(S : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hc)
    have h4 : 0 ≤ l1On h R / √(S : ℝ) := div_nonneg (l1On_nonneg h R) (Real.sqrt_nonneg _)
    have h5 : l2On h R ≤ √(S : ℝ) * t + l1On h R / √(S : ℝ) := by
      have := mul_le_mul_of_nonneg_right h3 ht; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h5 hK)
  intro N
  induction N with
  | zero => intro R hc; exact base R (by omega)
  | succ N ih =>
    intro R hc hd t ht hR
    by_cases hcS : R.card ≤ S
    · exact base R hcS hd t ht hR
    · push Not at hcS
      obtain ⟨T2, hT2R, hT2c, hT2top⟩ := top_exists h R S hcS.le
      have hR'c : (R \ T2).card ≤ N := by rw [Finset.card_sdiff_of_subset hT2R]; omega
      have hdT2 : Disjoint U T2 := Finset.disjoint_of_subset_right hT2R hd
      have hdR' : Disjoint U (R \ T2) := Finset.disjoint_of_subset_right Finset.sdiff_subset hd
      have ht' : 0 ≤ l1On h T2 / S := div_nonneg (l1On_nonneg h T2) hSpos.le
      have hR' : ∀ k ∈ R \ T2, |h k| ≤ l1On h T2 / S := by
        intro k hk
        have : ∑ j ∈ T2, |h k| ≤ ∑ j ∈ T2, |h j| :=
          Finset.sum_le_sum fun j hj => hT2top j hj k hk
        rw [Finset.sum_const, hT2c, nsmul_eq_mul] at this
        rw [le_div_iff₀ hSpos]; unfold l1On; linarith
      have ih' := ih (R \ T2) hR'c hdR' _ ht' hR'
      rw [sqrt_avg S hS] at ih'
      have hsplit : rs h R = rs h T2 + rs h (R \ T2) := by
        rw [← rs_split h T2 (R \ T2) Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hT2R]
      have h1 := hrop T2 (rs h T2) hdT2 hT2c.le (rs_supp h T2)
      rw [l2Norm_rs] at h1
      have h2 := l2On_le_card h T2 t ht (fun k hk => hR k (hT2R hk))
      rw [hT2c] at h2
      have hsum : l1On h R = l1On h T2 + l1On h (R \ T2) := by
        unfold l1On; rw [← Finset.sum_sdiff hT2R]; ring
      have e1 : |(X.mulVec v) ⬝ᵥ (X.mulVec (rs h T2))| ≤ θ * l2Norm v * (√(S : ℝ) * t) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hK)
      rw [hsplit, Matrix.mulVec_add, dotProduct_add]
      have e3 := abs_add_le ((X.mulVec v) ⬝ᵥ (X.mulVec (rs h T2)))
        ((X.mulVec v) ⬝ᵥ (X.mulVec (rs h (R \ T2))))
      have e4 : θ * l2Norm v * (√(S : ℝ) * t + l1On h R / √(S : ℝ)) =
          θ * l2Norm v * (√(S : ℝ) * t) +
            θ * l2Norm v * (l1On h T2 / √(S : ℝ) + l1On h (R \ T2) / √(S : ℝ)) := by
        rw [hsum, add_div]; ring
      rw [e4]
      linarith

/-- Lemma 3.1 (D1). -/
theorem lemma31 {n p S : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hS : 1 ≤ S)
    (hRIP : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (T0 T1 : Finset (Fin p)) (hT0 : T0.card = S) (h : Fin p → ℝ)
    (hT1 : IsTopBlock h T0 T1 S) :
    l2On h (T0 ∪ T1) ≤
        1 / (1 - restrictedIsometryConst X (2 * S)) *
            Real.sqrt (∑ j ∈ T0 ∪ T1, (∑ i, X i j * X.mulVec h i) ^ 2) +
          restrictedOrthogonalityConst X S (2 * S) /
              ((1 - restrictedIsometryConst X (2 * S)) * Real.sqrt S) * l1On h T0ᶜ ∧
      l2Norm h ^ 2 ≤ l2On h (T0 ∪ T1) ^ 2 + (S : ℝ)⁻¹ * l1On h T0ᶜ ^ 2 := by
  classical
  have hθ0 : 0 ≤ restrictedOrthogonalityConst X S (2 * S) := roc_nonneg X S (2 * S)
  have hu : 0 < 1 - restrictedIsometryConst X (2 * S) := by linarith
  have hTB := hT1
  obtain ⟨hT1sub, hT1c, hT1top⟩ := hT1
  have hdisj : Disjoint T0 T1 := by
    rw [Finset.disjoint_left]; intro j hj0 hj1; exact (Finset.mem_compl.1 (hT1sub hj1)) hj0
  have hcard : (T0 ∪ T1).card ≤ 2 * S := by rw [Finset.card_union_of_disjoint hdisj]; omega
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hsp : 0 < √(S : ℝ) := Real.sqrt_pos.2 hSpos
  have hReq : (T0 ∪ T1)ᶜ = T0ᶜ \ T1 := by
    ext k; simp only [Finset.mem_compl, Finset.mem_union, not_or, Finset.mem_sdiff]
  have hhv : h = rs h (T0 ∪ T1) + rs h (T0 ∪ T1)ᶜ := by
    funext j; simp only [rs, Pi.add_apply, Finset.mem_compl]
    by_cases hj : j ∈ T0 ∪ T1 <;> simp [hj]
  have hdUR : Disjoint (T0 ∪ T1) (T0 ∪ T1)ᶜ := disjoint_compl_right
  have ht : 0 ≤ l1On h T1 / S := div_nonneg (l1On_nonneg h T1) hSpos.le
  have hRt : ∀ k ∈ (T0 ∪ T1)ᶜ, |h k| ≤ l1On h T1 / S := by
    intro k hk
    rw [hReq] at hk
    have : ∑ j ∈ T1, |h k| ≤ ∑ j ∈ T1, |h j| := Finset.sum_le_sum fun j hj => hT1top j hj k hk
    rw [Finset.sum_const, hT1c, nsmul_eq_mul] at this
    rw [le_div_iff₀ hSpos]; unfold l1On; linarith
  have hrop : ∀ (U' : Finset (Fin p)) (v' : Fin p → ℝ), Disjoint (T0 ∪ T1) U' → U'.card ≤ S →
      SupportedOn v' U' →
      |(X.mulVec (rs h (T0 ∪ T1))) ⬝ᵥ (X.mulVec v')| ≤
        restrictedOrthogonalityConst X S (2 * S) * l2Norm (rs h (T0 ∪ T1)) * l2Norm v' := by
    intro U' v' hd hc hv'
    have := rop_bound X S (2 * S) U' (T0 ∪ T1) hd.symm hc hcard v' (rs h (T0 ∪ T1)) hv'
      (rs_supp h _)
    rw [dotProduct_comm] at this
    linarith
  have hsh := shell X S hS _ hθ0 (T0 ∪ T1) (rs h (T0 ∪ T1)) hrop h _ (T0 ∪ T1)ᶜ le_rfl hdUR _
    ht hRt
  have hL : √(S : ℝ) * (l1On h T1 / S) + l1On h (T0 ∪ T1)ᶜ / √(S : ℝ) =
      l1On h T0ᶜ / √(S : ℝ) := by
    rw [sqrt_avg S hS, ← add_div, hReq]
    congr 1
    unfold l1On; rw [← Finset.sum_sdiff hT1sub]; ring
  rw [hL] at hsh
  have hvn : l2Norm (rs h (T0 ∪ T1)) = l2On h (T0 ∪ T1) := l2Norm_rs h _
  set A := Real.sqrt (∑ j ∈ T0 ∪ T1, (∑ i, X i j * X.mulVec h i) ^ 2) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hdotA : (X.mulVec (rs h (T0 ∪ T1))) ⬝ᵥ (X.mulVec h) ≤ l2On h (T0 ∪ T1) * A := by
    rw [← sum_mul_corr]
    have e : ∑ j, rs h (T0 ∪ T1) j * corr X h j =
        ∑ j ∈ T0 ∪ T1, h j * (∑ i, X i j * X.mulVec h i) := by
      simp only [rs, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [corr_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hdecomp : l2Norm (X.mulVec (rs h (T0 ∪ T1))) ^ 2 =
      (X.mulVec (rs h (T0 ∪ T1))) ⬝ᵥ (X.mulVec h) -
        (X.mulVec (rs h (T0 ∪ T1))) ⬝ᵥ (X.mulVec (rs h (T0 ∪ T1)ᶜ)) := by
    have : X.mulVec h = X.mulVec (rs h (T0 ∪ T1)) + X.mulVec (rs h (T0 ∪ T1)ᶜ) := by
      conv_lhs => rw [hhv]
      exact Matrix.mulVec_add _ _ _
    rw [l2Norm_sq_dot, this, dotProduct_add]; ring
  have hlow := rip_lower X (2 * S) (T0 ∪ T1) hcard (rs h (T0 ∪ T1)) (rs_supp h _)
  rw [hvn] at hlow hsh
  have hab := le_abs_self ((X.mulVec (rs h (T0 ∪ T1))) ⬝ᵥ (X.mulVec (rs h (T0 ∪ T1)ᶜ)))
  have hneg := neg_abs_le ((X.mulVec (rs h (T0 ∪ T1))) ⬝ᵥ (X.mulVec (rs h (T0 ∪ T1)ᶜ)))
  set x := l2On h (T0 ∪ T1) with hx
  set L := l1On h T0ᶜ with hLdef
  set δ := restrictedIsometryConst X (2 * S) with hδ
  set θ := restrictedOrthogonalityConst X S (2 * S) with hθ
  have hL0 : 0 ≤ L := l1On_nonneg h _
  have hx0 : 0 ≤ x := l2On_nonneg h _
  have key : (1 - δ) * x ^ 2 ≤ x * A + θ * x * (L / √(S : ℝ)) := by
    rw [hdecomp] at hlow
    linarith
  refine ⟨?_, ?_⟩
  · have hRHS : 1 / (1 - δ) * A + θ / ((1 - δ) * √(S : ℝ)) * L =
        (A + θ * (L / √(S : ℝ))) / (1 - δ) := by
      field_simp
    rw [hRHS, le_div_iff₀ hu]
    rcases hx0.eq_or_lt with h0 | h0
    · rw [← h0]
      have : 0 ≤ θ * (L / √(S : ℝ)) := mul_nonneg hθ0 (div_nonneg hL0 hsp.le)
      linarith
    · have : x * ((1 - δ) * x) ≤ x * (A + θ * (L / √(S : ℝ))) := by nlinarith
      have := le_of_mul_le_mul_left this h0
      linarith
  · have h1 := tail_bound h T0 T1 S (by omega) hTB
    have h2 : l2Norm h ^ 2 = x ^ 2 + ∑ k ∈ (T0 ∪ T1)ᶜ, h k ^ 2 := by
      rw [l2Norm_sq, hx]
      unfold l2On
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Finset.sum_add_sum_compl]
    rw [h2, inv_mul_eq_div]
    linarith


lemma cone {p : ℕ} (β h : Fin p → ℝ) (T0 : Finset (Fin p))
    (hβ : SupportedOn β T0) (hle : l1Norm (β + h) ≤ l1Norm β) :
    l1On h T0ᶜ ≤ l1On h T0 := by
  unfold l1Norm at hle
  unfold l1On
  rw [← Finset.sum_add_sum_compl T0 (fun j => |(β + h) j|),
    ← Finset.sum_add_sum_compl T0 (fun j => |β j|)] at hle
  have h1 : ∑ j ∈ T0ᶜ, |(β + h) j| = ∑ j ∈ T0ᶜ, |h j| := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have : β j = 0 := hβ j (Finset.mem_compl.mp hj)
    simp [Pi.add_apply, this]
  have h2 : ∑ j ∈ T0ᶜ, |β j| = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    simp [hβ j (Finset.mem_compl.mp hj)]
  have h3 : ∑ j ∈ T0, (|β j| - |h j|) ≤ ∑ j ∈ T0, |(β + h) j| := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := abs_sub_abs_le_abs_sub (β j) (-(h j))
    simp only [sub_neg_eq_add, abs_neg] at this
    simpa [Pi.add_apply] using this
  rw [Finset.sum_sub_distrib] at h3
  linarith

lemma tube {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (β b : Fin p → ℝ)
    (z : Fin n → ℝ) (lam : ℝ)
    (hz : ∀ j : Fin p, |∑ i, X i j * z i| ≤ lam)
    (hb : DantzigFeasible X (X.mulVec β + z) lam b) :
    ∀ j : Fin p, |∑ i, X i j * X.mulVec (b - β) i| ≤ 2 * lam := by
  intro j
  have h1 := hz j
  have h2 := hb j
  have key : ∑ i, X i j * X.mulVec (b - β) i
      = ∑ i, X i j * z i - ∑ i, X i j * ((X.mulVec β + z) i - X.mulVec b i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [key]
  calc |∑ i, X i j * z i - ∑ i, X i j * ((X.mulVec β + z) i - X.mulVec b i)|
      ≤ |∑ i, X i j * z i| + |∑ i, X i j * ((X.mulVec β + z) i - X.mulVec b i)| := abs_sub _ _
    _ ≤ lam + lam := add_le_add h1 h2
    _ = 2 * lam := by ring

lemma l1_le_sqrt_card {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    l1On δ J ≤ √(J.card : ℝ) * l2On δ J := by
  unfold l1On l2On
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  have := sq_sum_le_card_mul_sum_sq (s := J) (f := fun j => |δ j|)
  simpa [sq_abs] using this

lemma l2On_mono {M : ℕ} (δ : Fin M → ℝ) {J K : Finset (Fin M)} (h : J ⊆ K) :
    l2On δ J ≤ l2On δ K := by
  unfold l2On
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _))

/-- `l2_bound_on_noise_event` (D2). -/
theorem noise {n p S : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hS : 1 ≤ S) (hSp : 3 * S ≤ p)
    (hRIP : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (β : Fin p → ℝ) (hβ : IsSparse β S) (z : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hz : ∀ j : Fin p, |∑ i, X i j * z i| ≤ lam) (b : Fin p → ℝ)
    (hb : IsDantzigSelector X (X.mulVec β + z) lam b) :
    l2Norm (b - β) ^ 2 ≤
      (4 / (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S))) ^ 2
        * lam ^ 2 * S := by
  classical
  obtain ⟨T, hTc, hTs⟩ := hβ
  obtain ⟨T0, hTT0, -, hT0c⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ T) hTc
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hβ0 : SupportedOn β T0 := fun j hj => hTs j (fun h => hj (hTT0 h))
  have hfeas : DantzigFeasible X (X.mulVec β + z) lam β := by
    intro j
    have : ∀ i, (X.mulVec β + z) i - X.mulVec β i = z i := fun i => by simp
    simp only [this]; exact hz j
  have htube := tube X β b z lam hz hb.1
  have hle : l1Norm (β + (b - β)) ≤ l1Norm β := by
    have : β + (b - β) = b := by abel
    rw [this]; exact hb.2 β hfeas
  have hcone := cone β (b - β) T0 hβ0 hle
  set h := b - β with hhdef
  have hcc : S ≤ T0ᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨T1, hT1sub, hT1c, hT1top⟩ := top_exists h T0ᶜ S hcc
  have hTB : IsTopBlock h T0 T1 S := ⟨hT1sub, hT1c, hT1top⟩
  obtain ⟨hA, hB⟩ := lemma31 X hS hRIP T0 T1 hT0c h hTB
  have hdisj : Disjoint T0 T1 := by
    rw [Finset.disjoint_left]; intro j hj0 hj1; exact (Finset.mem_compl.1 (hT1sub hj1)) hj0
  have hcardU : (T0 ∪ T1).card = 2 * S := by
    rw [Finset.card_union_of_disjoint hdisj, hT0c, hT1c]; ring
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hsp : 0 < √(S : ℝ) := Real.sqrt_pos.2 hSpos
  set A := Real.sqrt (∑ j ∈ T0 ∪ T1, (∑ i, X i j * X.mulVec h i) ^ 2) with hAdef
  have hA2 : A ≤ 2 * lam * √(2 * (S : ℝ)) := by
    have : ∑ j ∈ T0 ∪ T1, (∑ i, X i j * X.mulVec h i) ^ 2 ≤ ∑ j ∈ T0 ∪ T1, (2 * lam) ^ 2 :=
      Finset.sum_le_sum fun j _ => by
        have := htube j; have := abs_nonneg (∑ i, X i j * X.mulVec h i)
        have := sq_abs (∑ i, X i j * X.mulVec h i); nlinarith
    rw [Finset.sum_const, hcardU, nsmul_eq_mul] at this
    calc A ≤ √(((2 * S : ℕ) : ℝ) * (2 * lam) ^ 2) := Real.sqrt_le_sqrt this
      _ = 2 * lam * √(2 * (S : ℝ)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]; push_cast; ring
  set x := l2On h (T0 ∪ T1) with hx
  set L := l1On h T0ᶜ with hLdef
  have hx0 : 0 ≤ x := l2On_nonneg h _
  have hL0 : 0 ≤ L := l1On_nonneg h _
  have hLx : L ≤ √(S : ℝ) * x := by
    have h1 := l1_le_sqrt_card h T0
    rw [hT0c] at h1
    have h2 : l2On h T0 ≤ x := l2On_mono h Finset.subset_union_left
    calc L ≤ l1On h T0 := hcone
      _ ≤ √(S : ℝ) * l2On h T0 := h1
      _ ≤ √(S : ℝ) * x := mul_le_mul_of_nonneg_left h2 hsp.le
  set δ := restrictedIsometryConst X (2 * S) with hδ
  set θ := restrictedOrthogonalityConst X S (2 * S) with hθ
  have hθ0 : 0 ≤ θ := roc_nonneg X S (2 * S)
  have hu : 0 < 1 - δ := by linarith
  have hD : 0 < 1 - δ - θ := by linarith
  have hc0 : 0 ≤ θ / ((1 - δ) * √(S : ℝ)) := div_nonneg hθ0 (mul_pos hu hsp).le
  have e1 : θ / ((1 - δ) * √(S : ℝ)) * (√(S : ℝ) * x) = θ * x / (1 - δ) := by
    field_simp
  have e2 : x ≤ (A + θ * x) / (1 - δ) := by
    calc x ≤ 1 / (1 - δ) * A + θ / ((1 - δ) * √(S : ℝ)) * L := hA
      _ ≤ 1 / (1 - δ) * A + θ / ((1 - δ) * √(S : ℝ)) * (√(S : ℝ) * x) :=
          by linarith [mul_le_mul_of_nonneg_left hLx hc0]
      _ = (A + θ * x) / (1 - δ) := by rw [e1, add_div]; ring
  rw [le_div_iff₀ hu] at e2
  have e3 : (1 - δ - θ) * x ≤ 2 * lam * √(2 * (S : ℝ)) := by linarith
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * S by positivity)
  have hx2 : (1 - δ - θ) ^ 2 * x ^ 2 ≤ 8 * lam ^ 2 * S := by
    have := mul_self_le_mul_self (mul_nonneg hD.le hx0) e3
    have e4 : (2 * lam * √(2 * (S : ℝ))) * (2 * lam * √(2 * (S : ℝ))) = 8 * lam ^ 2 * S := by
      rw [show (2 * lam * √(2 * (S : ℝ))) * (2 * lam * √(2 * (S : ℝ))) =
        4 * lam ^ 2 * (√(2 * (S : ℝ))) ^ 2 by ring, hs2]; ring
    rw [e4] at this
    linarith
  have hL2 : L ^ 2 ≤ S * x ^ 2 := by
    have := mul_self_le_mul_self hL0 hLx
    have hs := Real.sq_sqrt hSpos.le
    have e4 : (√(S : ℝ) * x) * (√(S : ℝ) * x) = S * x ^ 2 := by
      rw [show (√(S : ℝ) * x) * (√(S : ℝ) * x) = (√(S : ℝ)) ^ 2 * x ^ 2 by ring, hs]
    rw [e4] at this
    linarith
  have hB' : l2Norm h ^ 2 ≤ 2 * x ^ 2 := by
    have : (S : ℝ)⁻¹ * L ^ 2 ≤ x ^ 2 := by
      rw [inv_mul_le_iff₀ hSpos]; linarith
    linarith
  have hfin : (4 / (1 - δ - θ)) ^ 2 * lam ^ 2 * S = (16 * lam ^ 2 * S) / (1 - δ - θ) ^ 2 := by
    rw [div_pow]; ring
  rw [hfin, le_div_iff₀ (by positivity)]
  linarith [mul_le_mul_of_nonneg_right hB' (sq_nonneg (1 - δ - θ))]

/-- a Dantzig selector exists whenever the program is feasible (D4). -/
theorem exists_ds {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (b0 : Fin p → ℝ) (hb0 : DantzigFeasible X y r b0) : ∃ b, IsDantzigSelector X y r b := by
  have hcont : Continuous (fun b : Fin p → ℝ => l1Norm b) := by
    unfold l1Norm; fun_prop
  have hFc : IsClosed {b : Fin p → ℝ | DantzigFeasible X y r b} := by
    simp only [DantzigFeasible, Set.ofPred_forall]
    refine isClosed_iInter fun j => isClosed_le ?_ continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  set K := {b : Fin p → ℝ | DantzigFeasible X y r b} ∩ {b | l1Norm b ≤ l1Norm b0} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (hFc.inter (isClosed_le hcont continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin p → ℝ)) (r := l1Norm b0)).subset ?_
    intro b hb
    rw [Metric.mem_closedBall, dist_zero_right]
    have hr : 0 ≤ l1Norm b0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact (abs_le_l1Norm b i).trans hb.2
  obtain ⟨b, hbK, hmin⟩ := hKc.exists_isMinOn ⟨b0, Set.mem_inter hb0 (le_refl (l1Norm b0))⟩
    hcont.continuousOn
  refine ⟨b, hbK.1, fun b' hb' => ?_⟩
  by_cases h : l1Norm b' ≤ l1Norm b0
  · exact isMinOn_iff.1 hmin b' (Set.mem_inter hb' h)
  · exact hbK.2.trans (not_le.1 h).le


/-! ### strict Gaussian max tail (D3) -/

lemma pdf_eq (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]

lemma pdf_tendsto :
    Filter.Tendsto (gaussianPDFReal 0 1) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at h
  have hf : gaussianPDFReal 0 1 = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
    funext y; rw [pdf_eq]; congr 2; ring
  rw [hf]
  exact h

lemma pdf_deriv (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  have hf : gaussianPDFReal 0 1 = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
    funext y; rw [pdf_eq]; congr 2; ring
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [hf]
  exact h2.congr_deriv (by ring)

lemma tail_strict (u : ℝ) (hu : 0 < u) :
    gaussianReal 0 1 (Set.Ioi u) < ENNReal.ofReal (gaussianPDFReal 0 1 u / u) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.ofReal_lt_ofReal_iff (div_pos (gaussianPDFReal_pos 0 1 u one_ne_zero) hu)]
  have hderiv : ∀ v ∈ Set.Ici u, HasDerivAt (fun v => -gaussianPDFReal 0 1 v / u)
      (v / u * gaussianPDFReal 0 1 v) v := by
    intro v _
    exact ((pdf_deriv v).neg.div_const u).congr_deriv (by ring)
  have hpos : ∀ v ∈ Set.Ioi u, 0 ≤ v / u * gaussianPDFReal 0 1 v := by
    intro v hv
    exact mul_nonneg (div_nonneg (hu.trans hv).le hu.le) (gaussianPDFReal_nonneg _ _ _)
  have hlim : Filter.Tendsto (fun v => -gaussianPDFReal 0 1 v / u) Filter.atTop
      (nhds (-0 / u)) := (pdf_tendsto.neg).div_const u
  have hI := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hφi : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi u) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hg : 0 < ∫ x in Set.Ioi u, (x / u * gaussianPDFReal 0 1 x - gaussianPDFReal 0 1 x) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsupp : Function.support
          (fun x => x / u * gaussianPDFReal 0 1 x - gaussianPDFReal 0 1 x) ∩ Set.Ioi u
          = Set.Ioi u := by
        ext x
        simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
        refine ⟨fun h => h.2, fun hx => ⟨?_, hx⟩⟩
        have h1 := gaussianPDFReal_pos 0 1 x one_ne_zero
        have h2 : 1 < x / u := (one_lt_div hu).2 hx
        have : 0 < x / u * gaussianPDFReal 0 1 x - gaussianPDFReal 0 1 x := by nlinarith
        exact this.ne'
      rw [hsupp, Real.volume_Ioi]; exact ENNReal.zero_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h1 := gaussianPDFReal_nonneg 0 1 x
      have h2 : 1 < x / u := (one_lt_div hu).2 hx
      simp only [Pi.zero_apply]; nlinarith
    · exact hint.sub hφi
  rw [integral_sub hint hφi] at hg
  have : -0 / u - -gaussianPDFReal 0 1 u / u = gaussianPDFReal 0 1 u / u := by ring
  linarith

lemma abs_tail_strict (u : ℝ) (hu : 0 < u) :
    gaussianReal 0 1 {x | u < |x|} < 2 * ENNReal.ofReal (gaussianPDFReal 0 1 u / u) := by
  have hset : {x : ℝ | u < |x|} = Set.Ioi u ∪ (fun x => -x) ⁻¹' Set.Ioi u := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_preimage]
    exact lt_abs
  rw [hset]
  refine (measure_union_le _ _).trans_lt ?_
  have h2 : gaussianReal 0 1 ((fun x => -x) ⁻¹' Set.Ioi u) = gaussianReal 0 1 (Set.Ioi u) := by
    rw [← Measure.map_apply measurable_neg measurableSet_Ioi, gaussianReal_map_neg, neg_zero]
  rw [h2, two_mul]
  exact ENNReal.add_lt_add (tail_strict u hu) (tail_strict u hu)

lemma law {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : Fin n → ℝ) (hc : ∑ i, c i ^ 2 = 1)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 1) P) (hind : iIndepFun z P) :
    P.map (fun ω => ∑ i, c i * z i ω) = gaussianReal 0 1 := by
  set Y : Fin n → Ω → ℝ := fun i ω => c i * z i ω with hY
  have hYlaw' : ∀ i, ∃ v : NNReal, (v : ℝ) = c i ^ 2 ∧ HasLaw (Y i) (gaussianReal 0 v) P := by
    intro i
    have h := gaussianReal_const_mul (hz i) (c i)
    rw [mul_zero] at h
    refine ⟨_, ?_, h⟩
    rw [NNReal.coe_mul, NNReal.coe_one, mul_one]; rfl
  choose v hv hYlaw using hYlaw'
  have hYind : iIndepFun Y P := hind.comp (fun i x => c i * x) (fun i => by fun_prop)
  have hG : HasGaussianLaw (fun ω => ∑ i, Y i ω) P :=
    hYind.hasGaussianLaw_fun_sum (fun i => (hYlaw i).hasGaussianLaw)
  have hmem : ∀ i, MemLp (Y i) 2 P := by
    intro i
    have h0 : MemLp id (2 : ENNReal) (P.map (Y i)) := by
      rw [(hYlaw i).map_eq]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hYlaw i).aemeasurable).1 h0
  have hmean : P[fun ω => ∑ i, Y i ω] = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable one_le_two)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [(hYlaw i).integral_eq, integral_id_gaussianReal]
  have hvar : Var[fun ω => ∑ i, Y i ω; P] = 1 := by
    have hfn : (fun ω => ∑ i, Y i ω) = ∑ i, Y i := by
      funext ω; simp [Finset.sum_apply]
    rw [hfn, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hYind.indepFun hij)]
    have : ∀ i, Var[Y i; P] = c i ^ 2 := by
      intro i
      rw [(hYlaw i).variance_eq, variance_id_gaussianReal, hv i]
    simp only [this]
    rw [hc]
  show P.map (fun ω => ∑ i, Y i ω) = gaussianReal 0 1
  rw [hG.map_eq_gaussianReal, hmean, hvar]
  simp

lemma max_tail_strict {n p : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hp : 1 ≤ p) (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitNormColumns X)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 1) P) (hind : iIndepFun z P)
    (u : ℝ) (hu : 0 < u) :
    P {ω | ∃ j : Fin p, u < |∑ i, X i j * z i ω|} <
      ENNReal.ofReal
        (2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2)) / u) := by
  classical
  have hset : {ω | ∃ j : Fin p, u < |∑ i, X i j * z i ω|}
      = ⋃ j, {ω | u < |∑ i, X i j * z i ω|} := by
    ext ω; simp
  rw [hset]
  refine (measure_iUnion_fintype_le P _).trans_lt ?_
  have hj : ∀ j, P {ω | u < |∑ i, X i j * z i ω|}
      < 2 * ENNReal.ofReal (gaussianPDFReal 0 1 u / u) := by
    intro j
    have hc : ∑ i, X i j ^ 2 = 1 := by
      have h := hX j
      unfold l2Norm column at h
      rwa [Real.sqrt_eq_one] at h
    have hmap := law P (fun i => X i j) hc z hz hind
    have hae : AEMeasurable (fun ω => ∑ i, X i j * z i ω) P := by
      have := fun i => (hz i).aemeasurable
      fun_prop
    have hms : MeasurableSet {x : ℝ | u < |x|} :=
      measurableSet_lt measurable_const measurable_abs
    calc P {ω | u < |∑ i, X i j * z i ω|}
        = P.map (fun ω => ∑ i, X i j * z i ω) {x : ℝ | u < |x|} := by
          rw [Measure.map_apply_of_aemeasurable hae hms]; rfl
      _ = gaussianReal 0 1 {x : ℝ | u < |x|} := by rw [hmap]
      _ < _ := abs_tail_strict u hu
  calc ∑ j, P {ω | u < |∑ i, X i j * z i ω|}
      < ∑ _j : Fin p, 2 * ENNReal.ofReal (gaussianPDFReal 0 1 u / u) :=
        ENNReal.sum_lt_sum_of_nonempty ⟨⟨0, hp⟩, Finset.mem_univ _⟩ (fun j _ => hj j)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pdf_eq]
      rw [show 2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2)) / u
          = (p : ℝ) * (2 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2) / u)) by ring]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- the final real inequality. -/
lemma final_ineq (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : 0 ≤ a) :
    2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(Real.sqrt (2 * (1 + a) * Real.log p)) ^ 2 / 2)) /
        Real.sqrt (2 * (1 + a) * Real.log p) ≤
      1 / (Real.sqrt (Real.pi * Real.log p) * (p : ℝ) ^ a) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < p := by linarith
  have hlog : 0 < Real.log p := Real.log_pos hp1
  set lam := Real.sqrt (2 * (1 + a) * Real.log p) with hlam
  have hlam2 : lam ^ 2 = 2 * (1 + a) * Real.log p := Real.sq_sqrt (by positivity)
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have hpe : (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hpos).symm
  have hexp : Real.exp (-lam ^ 2 / 2) * p = (Real.exp (Real.log p * a))⁻¹ := by
    calc Real.exp (-lam ^ 2 / 2) * p = Real.exp (-lam ^ 2 / 2) * Real.exp (Real.log p) := by
          rw [← hpe]
      _ = Real.exp (-lam ^ 2 / 2 + Real.log p) := (Real.exp_add _ _).symm
      _ = Real.exp (-(Real.log p * a)) := by rw [hlam2]; congr 1; ring
      _ = (Real.exp (Real.log p * a))⁻¹ := Real.exp_neg _
  rw [Real.rpow_def_of_pos hpos a]
  set E := Real.exp (Real.log p * a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hs2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsl : 0 < Real.sqrt (Real.pi * Real.log p) := Real.sqrt_pos.2 (by positivity)
  have hL : 2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-lam ^ 2 / 2)) / lam
      = 2 / (E * (Real.sqrt (2 * Real.pi) * lam)) := by
    have : 2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-lam ^ 2 / 2)) / lam
        = 2 * (Real.exp (-lam ^ 2 / 2) * p) / (Real.sqrt (2 * Real.pi) * lam) := by
      field_simp
    rw [this, hexp]
    field_simp
  rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]
  have hk : 2 * Real.sqrt (Real.pi * Real.log p) ≤ Real.sqrt (2 * Real.pi) * lam := by
    rw [hlam, ← Real.sqrt_mul (by positivity)]
    have : 2 * Real.sqrt (Real.pi * Real.log p) = Real.sqrt (4 * (Real.pi * Real.log p)) := by
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
    rw [this]
    apply Real.sqrt_le_sqrt
    have := Real.pi_pos
    nlinarith [mul_nonneg (mul_nonneg this.le ha) hlog.le]
  have := mul_le_mul_of_nonneg_left hk hE0.le
  linarith

end DS6

open CandesTao.Decoding MeasureTheory ProbabilityTheory DantzigSelector.Sparse in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n p S : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : UnitNormColumns X) (hS : 1 ≤ S) (hSp : 3 * S ≤ p)
    (hRIP : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (β : Fin p → ℝ) (hβ : IsSparse β S) (σ : ℝ) (hσ : 0 < σ)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 (σ ^ 2).toNNReal) P)
    (hind : iIndepFun z P) (a : ℝ) (ha : 0 ≤ a) :
    P {ω | ¬ ((∃ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                (Real.sqrt (2 * (1 + a) * Real.log p) * σ) b) ∧
            ∀ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                (Real.sqrt (2 * (1 + a) * Real.log p) * σ) b →
              l2Norm (b - β) ^ 2 ≤
                (4 / (1 - restrictedIsometryConst X (2 * S)
                    - restrictedOrthogonalityConst X S (2 * S))) ^ 2
                  * Real.sqrt (2 * (1 + a) * Real.log p) ^ 2 * S * σ ^ 2)} <
      ENNReal.ofReal (1 / (Real.sqrt (Real.pi * Real.log p) * (p : ℝ) ^ a)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hlam0 : 0 < Real.sqrt (2 * (1 + a) * Real.log p) := Real.sqrt_pos.2 (by positivity)
  have hfin := DS6.final_ineq p (by omega) a ha
  set lam := Real.sqrt (2 * (1 + a) * Real.log p) with hlam
  set w : Fin n → Ω → ℝ := fun i ω => σ⁻¹ * z i ω with hw
  have hwlaw : ∀ i, HasLaw (w i) (gaussianReal 0 1) P := by
    intro i
    have h := gaussianReal_const_mul (hz i) σ⁻¹
    rw [mul_zero] at h
    convert h using 2
    ext
    simp only [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg σ)]
    field_simp
  have hwind : iIndepFun w P := hind.comp (fun i x => σ⁻¹ * x) (fun i => by fun_prop)
  have hsub : {ω | ¬ ((∃ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω) (lam * σ) b) ∧
            ∀ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω) (lam * σ) b →
              l2Norm (b - β) ^ 2 ≤
                (4 / (1 - restrictedIsometryConst X (2 * S)
                    - restrictedOrthogonalityConst X S (2 * S))) ^ 2
                  * lam ^ 2 * S * σ ^ 2)} ⊆
      {ω | ∃ j : Fin p, lam < |∑ i, X i j * w i ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hc
    simp only [not_exists, not_lt] at hc
    apply hω
    have hzj : ∀ j : Fin p, |∑ i, X i j * z i ω| ≤ lam * σ := by
      intro j
      have e : ∑ i, X i j * z i ω = σ * ∑ i, X i j * w i ω := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show X i j * z i ω = σ * (X i j * (σ⁻¹ * z i ω))
        field_simp
      rw [e, abs_mul, abs_of_pos hσ]
      have := mul_le_mul_of_nonneg_left (hc j) hσ.le
      linarith
    have hfeas : DantzigFeasible X (X.mulVec β + fun i => z i ω) (lam * σ) β := by
      intro j
      have : ∀ i, (X.mulVec β + fun i => z i ω) i - X.mulVec β i = z i ω := fun i => by simp
      simp only [this]; exact hzj j
    refine ⟨DS6.exists_ds X _ _ β hfeas, fun b hb => ?_⟩
    have := DS6.noise X hS hSp hRIP β hβ (fun i => z i ω) (lam * σ) (mul_pos hlam0 hσ) hzj b hb
    calc _ ≤ _ := this
      _ = _ := by ring
  have hmt := DS6.max_tail_strict P (by omega) X hX w hwlaw hwind lam hlam0
  exact lt_of_le_of_lt (measure_mono hsub) (hmt.trans_le (ENNReal.ofReal_le_ofReal hfin))
