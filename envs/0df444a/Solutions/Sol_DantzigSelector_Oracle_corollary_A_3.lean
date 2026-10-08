-- Prove2me | solution 1 for DantzigSelector.Oracle.corollary_A_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:51:58.504228+00:00
-- url     : https://prove2.me/submissions/c68e08ed-e531-4548-93b0-70db27bd1af9

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

set_option autoImplicit false

open CandesTao.Decoding DantzigSelector.Sparse

namespace A3C

/-- correlation vector `Xᵀ X v`. -/
noncomputable def corr {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) : Fin p → ℝ :=
  X.transpose.mulVec (X.mulVec v)

lemma corr_apply {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) (j : Fin p) :
    corr X v j = ∑ i, (X.mulVec v) i * X i j := by
  unfold corr
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma corr_add {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v w : Fin p → ℝ) :
    corr X (v + w) = corr X v + corr X w := by
  simp only [corr, Matrix.mulVec_add]

lemma corr_sub {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (v w : Fin p → ℝ) :
    corr X (v - w) = corr X v - corr X w := by
  simp only [corr, Matrix.mulVec_sub]

lemma corr_smul {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (a : ℝ) (v : Fin p → ℝ) :
    corr X (a • v) = a • corr X v := by
  simp only [corr, Matrix.mulVec_smul]

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

lemma l2Norm_neg {m : ℕ} (x : Fin m → ℝ) : l2Norm (-x) = l2Norm x := by
  simp [l2Norm]

lemma l2Norm_add_le {m : ℕ} (x y : Fin m → ℝ) : l2Norm (x + y) ≤ l2Norm x + l2Norm y := by
  have hd := abs_dot_le x y
  have hle := le_abs_self (x ⬝ᵥ y)
  have e : ∑ i, (x + y) i ^ 2 = l2Norm x ^ 2 + 2 * (x ⬝ᵥ y) + l2Norm y ^ 2 := by
    rw [l2Norm_sq, l2Norm_sq]
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, dotProduct, Finset.mul_sum]
    congr 1; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  have h : ∑ i, (x + y) i ^ 2 ≤ (l2Norm x + l2Norm y) ^ 2 := by
    rw [e]; nlinarith
  calc l2Norm (x + y) ≤ √((l2Norm x + l2Norm y) ^ 2) := Real.sqrt_le_sqrt h
    _ = l2Norm x + l2Norm y := Real.sqrt_sq (add_nonneg (l2Norm_nonneg _) (l2Norm_nonneg _))

lemma l2Norm_sub_le {m : ℕ} (x y : Fin m → ℝ) : l2Norm (x - y) ≤ l2Norm x + l2Norm y := by
  have := l2Norm_add_le x (-y)
  rwa [l2Norm_neg, ← sub_eq_add_neg] at this

lemma l1Norm_sub_le {m : ℕ} (x y : Fin m → ℝ) : l1Norm (x - y) ≤ l1Norm x + l1Norm y := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa using abs_sub (x i) (y i)

lemma l2Norm_ite {m : ℕ} (E : Finset (Fin m)) (f : Fin m → ℝ) :
    l2Norm (fun j => if j ∈ E then f j else 0) = √(∑ j ∈ E, f j ^ 2) := by
  unfold l2Norm
  congr 1
  simp [ite_pow, Finset.sum_ite_mem]

lemma abs_le_l1Norm {m : ℕ} (x : Fin m → ℝ) (j : Fin m) : |x j| ≤ l1Norm x :=
  Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

lemma abs_le_l2Norm {m : ℕ} (x : Fin m → ℝ) (j : Fin m) : |x j| ≤ l2Norm x := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))

lemma l1_le_of_supp {m : ℕ} (x : Fin m → ℝ) (U : Finset (Fin m)) (hx : SupportedOn x U) :
    l1Norm x ≤ √(U.card : ℝ) * l2Norm x := by
  have h1 : l1Norm x = ∑ j ∈ U, |x j| := by
    unfold l1Norm
    exact (Finset.sum_subset (Finset.subset_univ U) (fun j _ hj => by simp [hx j hj])).symm
  have h2 : ∑ j ∈ U, x j ^ 2 = ∑ j, x j ^ 2 :=
    Finset.sum_subset (Finset.subset_univ U) (fun j _ hj => by simp [hx j hj])
  have h3 := Real.sum_mul_le_sqrt_mul_sqrt U (fun j => |x j|) (fun _ => 1)
  simp only [sq_abs, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h3
  rw [h1, l2Norm, ← h2]
  have := mul_comm (√(∑ j ∈ U, x j ^ 2)) (√(U.card : ℝ))
  linarith

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

lemma gram_solve {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (δ : ℝ) (hδ : δ < 1) (U : Finset (Fin p))
    (hlow : ∀ v : Fin p → ℝ, SupportedOn v U → (1 - δ) * l2Norm v ^ 2 ≤ l2Norm (X.mulVec v) ^ 2)
    (c0 : Fin p → ℝ) : ∃ β : Fin p → ℝ, SupportedOn β U ∧ ∀ j ∈ U, corr X β j = c0 j := by
  classical
  let Pf : (Fin p → ℝ) → (Fin p → ℝ) := fun v j => if j ∈ U then v j else 0
  have hPadd : ∀ v w, Pf (v + w) = Pf v + Pf w := fun v w => by
    funext j; simp only [Pf, Pi.add_apply]; split_ifs <;> simp
  have hPsmul : ∀ (a : ℝ) v, Pf (a • v) = a • Pf v := fun a v => by
    funext j; simp only [Pf, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
  let L : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
    { toFun := fun v j => if j ∈ U then corr X (Pf v) j else v j
      map_add' := fun v w => by
        funext j; simp only [hPadd, corr_add, Pi.add_apply]; split_ifs <;> rfl
      map_smul' := fun a v => by
        funext j; simp only [hPsmul, corr_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> rfl }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ j, (if j ∈ U then corr X (Pf v) j else v j) = 0 := fun j => congrFun hv j
    have hoff : ∀ j, j ∉ U → v j = 0 := fun j hj => by simpa [hj] using hv' j
    have hPv : Pf v = v := funext fun j => by
      by_cases hj : j ∈ U
      · simp [Pf, hj]
      · simp [Pf, hj, hoff j hj]
    have hon : ∀ j ∈ U, corr X v j = 0 := fun j hj => by simpa [hj, hPv] using hv' j
    have h0 : l2Norm (X.mulVec v) ^ 2 = 0 := by
      rw [l2Norm_sq_dot, ← sum_mul_corr]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j ∈ U
      · simp [hon j hj]
      · simp [hoff j hj]
    have h1 := hlow v hoff
    have h2 : l2Norm v ^ 2 = 0 := by
      have := sq_nonneg (l2Norm v); nlinarith
    rw [l2Norm_sq] at h2
    funext j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 h2 j
      (Finset.mem_univ _)
    simpa using this
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj c0
  refine ⟨Pf v, fun j hj => by simp [Pf, hj], fun j hj => ?_⟩
  have : (if j ∈ U then corr X (Pf v) j else v j) = c0 j := congrFun hv j
  simpa [hj] using this

lemma lemA1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S) (δ θ : ℝ) (hδ : δ < 1)
    (hθ : 0 ≤ θ)
    (hlow : ∀ (U : Finset (Fin p)) (v : Fin p → ℝ), U.card ≤ 2 * S → SupportedOn v U →
      (1 - δ) * l2Norm v ^ 2 ≤ l2Norm (X.mulVec v) ^ 2)
    (hrop : ∀ (U U' : Finset (Fin p)) (v v' : Fin p → ℝ), Disjoint U U' → U.card ≤ S →
      U'.card ≤ 2 * S → SupportedOn v U → SupportedOn v' U' →
      |(X.mulVec v) ⬝ᵥ (X.mulVec v')| ≤ θ * l2Norm v * l2Norm v')
    (T0 : Finset (Fin p)) (hT0 : T0.card ≤ 2 * S) (c0 : Fin p → ℝ) :
    ∃ β : Fin p → ℝ, ∃ E : Finset (Fin p), Disjoint E T0 ∧ E.card ≤ S ∧
      (∀ j ∈ T0, corr X β j = c0 j) ∧
      (∀ j, j ∉ T0 → j ∉ E → |corr X β j| ≤ θ / ((1 - δ) * √(S : ℝ)) * l2Norm c0) ∧
      √(∑ j ∈ E, corr X β j ^ 2) ≤ θ / (1 - δ) * l2Norm c0 ∧
      l2Norm β ≤ l2Norm c0 / (1 - δ) ∧ l1Norm β ≤ √(2 * (S : ℝ)) * l2Norm c0 / (1 - δ) := by
  classical
  have hu : 0 < 1 - δ := by linarith
  obtain ⟨β, hβs, hβc⟩ := gram_solve X δ hδ T0 (fun v hv => hlow T0 v hT0 hv) c0
  have hK0 : 0 ≤ l2Norm c0 := l2Norm_nonneg _
  have hdot : (X.mulVec β) ⬝ᵥ (X.mulVec β) = β ⬝ᵥ c0 := by
    rw [← sum_mul_corr]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ T0
    · rw [hβc j hj]
    · simp [hβs j hj]
  have hb0 := l2Norm_nonneg β
  have hl2 : (1 - δ) * l2Norm β ≤ l2Norm c0 := by
    have h1 := hlow T0 β hT0 hβs
    rw [l2Norm_sq_dot (X.mulVec β), hdot] at h1
    have h2 := le_trans (le_abs_self _) (abs_dot_le β c0)
    rcases hb0.eq_or_lt with h | h
    · rw [← h]; simpa using hK0
    · have : (1 - δ) * l2Norm β * l2Norm β ≤ l2Norm c0 * l2Norm β := by nlinarith
      exact le_of_mul_le_mul_right this h
  have hl2' : l2Norm β ≤ l2Norm c0 / (1 - δ) := by rw [le_div_iff₀ hu]; linarith
  have h5 : θ * l2Norm β ≤ θ / (1 - δ) * l2Norm c0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hu]
    nlinarith [mul_le_mul_of_nonneg_left hl2 hθ]
  have sub : ∀ E' : Finset (Fin p), Disjoint E' T0 → E'.card ≤ S →
      √(∑ j ∈ E', corr X β j ^ 2) ≤ θ * l2Norm β := by
    intro E' hd hc
    have hds : SupportedOn (fun j => if j ∈ E' then corr X β j else 0) E' :=
      fun j hj => by simp [hj]
    have key : (X.mulVec (fun j => if j ∈ E' then corr X β j else 0)) ⬝ᵥ (X.mulVec β)
        = ∑ j ∈ E', corr X β j ^ 2 := by
      rw [← sum_mul_corr]; simp [ite_mul, Finset.sum_ite_mem, sq]
    have h := hrop E' T0 _ β hd hc hT0 hds hβs
    rw [key, l2Norm_ite] at h
    have hs0 : 0 ≤ ∑ j ∈ E', corr X β j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hss := Real.sq_sqrt hs0
    have h' : √(∑ j ∈ E', corr X β j ^ 2) * √(∑ j ∈ E', corr X β j ^ 2) ≤
        √(∑ j ∈ E', corr X β j ^ 2) * (θ * l2Norm β) := by
      rw [← sq, hss]
      have := le_trans (le_abs_self _) h
      linarith
    rcases (Real.sqrt_nonneg (∑ j ∈ E', corr X β j ^ 2)).eq_or_lt with h0 | h0
    · rw [← h0]; exact mul_nonneg hθ hb0
    · exact le_of_mul_le_mul_left h' h0
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hsq : 0 < √(S : ℝ) := Real.sqrt_pos.2 hSpos
  have ha0 : 0 ≤ θ / ((1 - δ) * √(S : ℝ)) := div_nonneg hθ (mul_pos hu hsq).le
  let E := Finset.univ.filter
    (fun j => j ∉ T0 ∧ θ / ((1 - δ) * √(S : ℝ)) * l2Norm c0 < |corr X β j|)
  have hEd : Disjoint E T0 := Finset.disjoint_left.2 fun j hj => (Finset.mem_filter.1 hj).2.1
  have hEc : E.card ≤ S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨E', hE'sub, hE'card⟩ := Finset.exists_subset_card_eq hcon.le
    have hd' : Disjoint E' T0 := Finset.disjoint_of_subset_left hE'sub hEd
    have h1 := sub E' hd' hE'card.le
    have hne : E'.Nonempty := by rw [← Finset.card_pos, hE'card]; omega
    have h0 : 0 ≤ θ / ((1 - δ) * √(S : ℝ)) * l2Norm c0 := mul_nonneg ha0 hK0
    have h2 : ∑ j ∈ E', (θ / ((1 - δ) * √(S : ℝ)) * l2Norm c0) ^ 2 < ∑ j ∈ E', corr X β j ^ 2 :=
      Finset.sum_lt_sum_of_nonempty hne fun j hj => by
        have := (Finset.mem_filter.1 (hE'sub hj)).2.2
        have := sq_abs (corr X β j)
        nlinarith
    rw [Finset.sum_const, hE'card, nsmul_eq_mul] at h2
    have h3 : (S : ℝ) * (θ / ((1 - δ) * √(S : ℝ)) * l2Norm c0) ^ 2
        = (θ / (1 - δ) * l2Norm c0) ^ 2 := by
      have := hsq.ne'
      have := hu.ne'
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hSpos.le]
      field_simp
    have h4 : θ / (1 - δ) * l2Norm c0 < √(∑ j ∈ E', corr X β j ^ 2) := by
      rw [Real.lt_sqrt (mul_nonneg (div_nonneg hθ hu.le) hK0)]
      linarith
    linarith
  refine ⟨β, E, hEd, hEc, hβc, ?_, ?_, hl2', ?_⟩
  · intro j hj hjE
    have : ¬ (θ / ((1 - δ) * √(S : ℝ)) * l2Norm c0 < |corr X β j|) := fun h =>
      hjE (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj, h⟩)
    exact not_lt.1 this
  · exact (sub E hEd hEc).trans h5
  · have h1 := l1_le_of_supp β T0 hβs
    have h2 : √(T0.card : ℝ) ≤ √(2 * (S : ℝ)) := Real.sqrt_le_sqrt (by exact_mod_cast hT0)
    calc l1Norm β ≤ √(T0.card : ℝ) * l2Norm β := h1
      _ ≤ √(2 * (S : ℝ)) * (l2Norm c0 / (1 - δ)) := mul_le_mul h2 hl2' hb0 (Real.sqrt_nonneg _)
      _ = √(2 * (S : ℝ)) * l2Norm c0 / (1 - δ) := by ring

lemma iter {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S) (δ θ : ℝ) (hδ : δ < 1)
    (hθ : 0 ≤ θ)
    (hlow : ∀ (U : Finset (Fin p)) (v : Fin p → ℝ), U.card ≤ 2 * S → SupportedOn v U →
      (1 - δ) * l2Norm v ^ 2 ≤ l2Norm (X.mulVec v) ^ 2)
    (hrop : ∀ (U U' : Finset (Fin p)) (v v' : Fin p → ℝ), Disjoint U U' → U.card ≤ S →
      U'.card ≤ 2 * S → SupportedOn v U → SupportedOn v' U' →
      |(X.mulVec v) ⬝ᵥ (X.mulVec v')| ≤ θ * l2Norm v * l2Norm v')
    (T : Finset (Fin p)) (hT : T.card ≤ S) (c : Fin p → ℝ) (N : ℕ) :
    ∃ β : Fin p → ℝ, ∃ E : Finset (Fin p), ∃ e : Fin p → ℝ,
      Disjoint E T ∧ E.card ≤ S ∧ SupportedOn e E ∧
      l2Norm e ≤ (θ / (1 - δ)) ^ (N + 1) * l2Norm c ∧
      (∀ j ∈ T, corr X β j = c j) ∧
      (∀ j, j ∉ T → |corr X β j - e j| ≤
        θ / ((1 - δ) * √(S : ℝ)) * l2Norm c * ∑ k ∈ Finset.range (N + 1), (θ / (1 - δ)) ^ k) ∧
      l2Norm β ≤ l2Norm c / (1 - δ) * ∑ k ∈ Finset.range (N + 1), (θ / (1 - δ)) ^ k ∧
      l1Norm β ≤ √(2 * (S : ℝ)) * l2Norm c / (1 - δ) *
        ∑ k ∈ Finset.range (N + 1), (θ / (1 - δ)) ^ k := by
  classical
  have hu : 0 < 1 - δ := by linarith
  have hr0 : 0 ≤ θ / (1 - δ) := div_nonneg hθ hu.le
  have hsq : 0 < √(S : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hS)
  have ha0 : 0 ≤ θ / ((1 - δ) * √(S : ℝ)) := div_nonneg hθ (mul_pos hu hsq).le
  have hK0 : 0 ≤ l2Norm c := l2Norm_nonneg _
  induction N with
  | zero =>
    obtain ⟨β, E, hEd, hEc, hβc, hoff, hEn, hl2, hl1⟩ :=
      lemA1 X S hS δ θ hδ hθ hlow hrop T (by omega) c
    refine ⟨β, E, fun j => if j ∈ E then corr X β j else 0, hEd, hEc,
      fun j hj => by simp [hj], ?_, hβc, ?_, ?_, ?_⟩
    · rw [l2Norm_ite]; simpa using hEn
    · intro j hj
      by_cases hjE : j ∈ E
      · simp only [hjE, if_true, sub_self, abs_zero, zero_add, Finset.sum_range_one, pow_zero,
          mul_one]
        exact mul_nonneg ha0 hK0
      · simpa [hjE] using hoff j hj hjE
    · simpa using hl2
    · simpa using hl1
  | succ N ih =>
    obtain ⟨β, E, e, hEd, hEc, hes, hen, hβc, hres, hl2, hl1⟩ := ih
    have hTE : (T ∪ E).card ≤ 2 * S := (Finset.card_union_le _ _).trans (by omega)
    obtain ⟨β', E', hE'd, hE'c, hβ'c, hoff', hE'n, hl2', hl1'⟩ :=
      lemA1 X S hS δ θ hδ hθ hlow hrop (T ∪ E) hTE e
    have hE'T : Disjoint E' T := Finset.disjoint_of_subset_right Finset.subset_union_left hE'd
    have hE'E : Disjoint E' E := Finset.disjoint_of_subset_right Finset.subset_union_right hE'd
    have hpow : 0 ≤ (θ / (1 - δ)) ^ (N + 1) := pow_nonneg hr0 _
    refine ⟨β - β', E', fun j => if j ∈ E' then -corr X β' j else 0, hE'T, hE'c,
      fun j hj => by simp [hj], ?_, ?_, ?_, ?_, ?_⟩
    · rw [l2Norm_ite]
      simp only [neg_sq]
      calc _ ≤ θ / (1 - δ) * l2Norm e := hE'n
        _ ≤ θ / (1 - δ) * ((θ / (1 - δ)) ^ (N + 1) * l2Norm c) :=
            mul_le_mul_of_nonneg_left hen hr0
        _ = (θ / (1 - δ)) ^ (N + 1 + 1) * l2Norm c := by ring
    · intro j hj
      have hjE : j ∉ E := fun h => Finset.disjoint_left.1 hEd h hj
      rw [corr_sub, Pi.sub_apply, hβc j hj, hβ'c j (Finset.mem_union_left _ hj), hes j hjE,
        sub_zero]
    · intro j hj
      rw [corr_sub, Pi.sub_apply, Finset.sum_range_succ]
      have hA : 0 ≤ θ / ((1 - δ) * √(S : ℝ)) * l2Norm c * (θ / (1 - δ)) ^ (N + 1) :=
        mul_nonneg (mul_nonneg ha0 hK0) hpow
      have hr' := hres j hj
      by_cases hjE : j ∈ E
      · have h1 : corr X β' j = e j := hβ'c j (Finset.mem_union_right _ hjE)
        have h2 : j ∉ E' := fun h => Finset.disjoint_left.1 hE'E h hjE
        simp only [h1, h2, if_false, sub_zero]
        linarith
      · have he : e j = 0 := hes j hjE
        rw [he, sub_zero] at hr'
        by_cases hjE' : j ∈ E'
        · simp only [hjE', if_true, sub_neg_eq_add, sub_add_cancel]
          linarith
        · simp only [hjE', if_false, sub_zero]
          have h3 := hoff' j (by simp [hj, hjE]) hjE'
          have h4 : |corr X β j - corr X β' j| ≤ |corr X β j| + |corr X β' j| := abs_sub _ _
          have h5 : θ / ((1 - δ) * √(S : ℝ)) * l2Norm e ≤
              θ / ((1 - δ) * √(S : ℝ)) * ((θ / (1 - δ)) ^ (N + 1) * l2Norm c) :=
            mul_le_mul_of_nonneg_left hen ha0
          linarith
    · rw [Finset.sum_range_succ]
      have h1 := l2Norm_sub_le β β'
      have h5 : l2Norm e / (1 - δ) ≤ (θ / (1 - δ)) ^ (N + 1) * l2Norm c / (1 - δ) :=
        div_le_div_of_nonneg_right hen hu.le
      have : (θ / (1 - δ)) ^ (N + 1) * l2Norm c / (1 - δ) =
          l2Norm c / (1 - δ) * (θ / (1 - δ)) ^ (N + 1) := by ring
      linarith
    · rw [Finset.sum_range_succ]
      have h1 := l1Norm_sub_le β β'
      have h5 : √(2 * (S : ℝ)) * l2Norm e / (1 - δ) ≤
          √(2 * (S : ℝ)) * ((θ / (1 - δ)) ^ (N + 1) * l2Norm c) / (1 - δ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hen (Real.sqrt_nonneg _)) hu.le
      have : √(2 * (S : ℝ)) * ((θ / (1 - δ)) ^ (N + 1) * l2Norm c) / (1 - δ) =
          √(2 * (S : ℝ)) * l2Norm c / (1 - δ) * (θ / (1 - δ)) ^ (N + 1) := by ring
      linarith

lemma geom_le (δ θ : ℝ) (hδθ : δ + θ < 1) (hθ : 0 ≤ θ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (θ / (1 - δ)) ^ k ≤ (1 - δ) / (1 - δ - θ) := by
  have hu : 0 < 1 - δ := by linarith
  have hv : 0 < 1 - δ - θ := by linarith
  have hr0 : 0 ≤ θ / (1 - δ) := div_nonneg hθ hu.le
  have h := geom_sum_mul (θ / (1 - δ)) (N + 1)
  have hp := pow_nonneg hr0 (N + 1)
  rw [le_div_iff₀ hv]
  set r := θ / (1 - δ) with hr
  set A := ∑ k ∈ Finset.range (N + 1), r ^ k with hA
  have e1 : θ = (1 - δ) * r := by rw [hr]; field_simp
  rw [e1]
  have h' : (1 - δ) * (A * (r - 1)) = (1 - δ) * (r ^ (N + 1) - 1) := by rw [h]
  nlinarith [mul_nonneg hu.le hp]

lemma main_core {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S) (δ θ : ℝ)
    (hδθ : δ + θ < 1) (hθ : 0 ≤ θ)
    (hlow : ∀ (U : Finset (Fin p)) (v : Fin p → ℝ), U.card ≤ 2 * S → SupportedOn v U →
      (1 - δ) * l2Norm v ^ 2 ≤ l2Norm (X.mulVec v) ^ 2)
    (hrop : ∀ (U U' : Finset (Fin p)) (v v' : Fin p → ℝ), Disjoint U U' → U.card ≤ S →
      U'.card ≤ 2 * S → SupportedOn v U → SupportedOn v' U' →
      |(X.mulVec v) ⬝ᵥ (X.mulVec v')| ≤ θ * l2Norm v * l2Norm v')
    (T : Finset (Fin p)) (hT : T.card ≤ S) (c : Fin p → ℝ) :
    ∃ β : Fin p → ℝ, (∀ j ∈ T, corr X β j = c j) ∧
      (∀ j : Fin p, j ∉ T → |corr X β j| ≤ θ / ((1 - δ - θ) * Real.sqrt S) * l2Norm c) ∧
      l2Norm β ≤ 1 / (1 - δ - θ) * l2Norm c ∧
      l1Norm β ≤ Real.sqrt (2 * (S : ℝ)) / (1 - δ - θ) * l2Norm c := by
  have hu : 0 < 1 - δ := by linarith
  have hv : 0 < 1 - δ - θ := by linarith
  have hδ : δ < 1 := by linarith
  have hr0 : 0 ≤ θ / (1 - δ) := div_nonneg hθ hu.le
  have hr1 : θ / (1 - δ) < 1 := by rw [div_lt_one hu]; linarith
  have hsq : 0 < √(S : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hS)
  have hK0 : 0 ≤ l2Norm c := l2Norm_nonneg _
  have hR1 : 0 ≤ Real.sqrt (2 * (S : ℝ)) / (1 - δ - θ) * l2Norm c :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hv.le) hK0
  have hstage : ∀ N : ℕ, ∃ β : Fin p → ℝ, (∀ j ∈ T, corr X β j = c j) ∧
      (∀ j : Fin p, j ∉ T → |corr X β j| ≤ θ / ((1 - δ - θ) * Real.sqrt S) * l2Norm c +
        l2Norm c * (θ / (1 - δ)) * (θ / (1 - δ)) ^ N) ∧
      l2Norm β ≤ 1 / (1 - δ - θ) * l2Norm c ∧
      l1Norm β ≤ Real.sqrt (2 * (S : ℝ)) / (1 - δ - θ) * l2Norm c := by
    intro N
    obtain ⟨β, E, e, -, -, -, hen, hβc, hres, hl2, hl1⟩ :=
      iter X S hS δ θ hδ hθ hlow hrop T hT c N
    have hA := geom_le δ θ hδθ hθ N
    have hAn : 0 ≤ ∑ k ∈ Finset.range (N + 1), (θ / (1 - δ)) ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg hr0 _
    refine ⟨β, hβc, fun j hj => ?_, ?_, ?_⟩
    · have h1 := hres j hj
      have h2 := abs_le_l2Norm e j
      have h3 : |corr X β j| ≤ |corr X β j - e j| + |e j| := by
        have := abs_add_le (corr X β j - e j) (e j)
        rwa [sub_add_cancel] at this
      have h4 : θ / ((1 - δ) * √(S : ℝ)) * l2Norm c *
            ∑ k ∈ Finset.range (N + 1), (θ / (1 - δ)) ^ k ≤
          θ / ((1 - δ) * √(S : ℝ)) * l2Norm c * ((1 - δ) / (1 - δ - θ)) :=
        mul_le_mul_of_nonneg_left hA
          (mul_nonneg (div_nonneg hθ (mul_pos hu hsq).le) hK0)
      have h5 : θ / ((1 - δ) * √(S : ℝ)) * l2Norm c * ((1 - δ) / (1 - δ - θ)) =
          θ / ((1 - δ - θ) * Real.sqrt S) * l2Norm c := by
        have := hsq.ne'; have := hu.ne'; have := hv.ne'
        field_simp
      have h6 : (θ / (1 - δ)) ^ (N + 1) * l2Norm c =
          l2Norm c * (θ / (1 - δ)) * (θ / (1 - δ)) ^ N := by ring
      linarith
    · calc l2Norm β ≤ l2Norm c / (1 - δ) * ((1 - δ) / (1 - δ - θ)) :=
            hl2.trans (mul_le_mul_of_nonneg_left hA (div_nonneg hK0 hu.le))
        _ = 1 / (1 - δ - θ) * l2Norm c := by
            have := hu.ne'; have := hv.ne'
            field_simp
    · calc l1Norm β ≤ √(2 * (S : ℝ)) * l2Norm c / (1 - δ) * ((1 - δ) / (1 - δ - θ)) :=
            hl1.trans (mul_le_mul_of_nonneg_left hA
              (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK0) hu.le))
        _ = Real.sqrt (2 * (S : ℝ)) / (1 - δ - θ) * l2Norm c := by
            have := hu.ne'; have := hv.ne'
            field_simp
  choose β hβ using hstage
  have hmem : ∀ N, β N ∈ Metric.closedBall (0 : Fin p → ℝ)
      (Real.sqrt (2 * (S : ℝ)) / (1 - δ - θ) * l2Norm c) := by
    intro N
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR1]
    intro j
    rw [Real.norm_eq_abs]
    exact (abs_le_l1Norm _ j).trans (hβ N).2.2.2
  obtain ⟨b, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin p → ℝ) _).tendsto_subseq hmem
  have hcorr : Continuous (corr X) := by unfold corr; fun_prop
  have hcc : ∀ j, Continuous fun v => corr X v j := fun j => (continuous_apply j).comp hcorr
  have hl2c : Continuous fun v : Fin p → ℝ => l2Norm v := by unfold l2Norm; fun_prop
  have hl1c : Continuous fun v : Fin p → ℝ => l1Norm v := by unfold l1Norm; fun_prop
  refine ⟨b, fun j hj => ?_, fun j hj => ?_, ?_, ?_⟩
  · have := (isClosed_eq (hcc j) continuous_const).mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun N => (hβ (φ N)).1 j hj)
    exact this
  · have hM : ∀ M : ℕ, |corr X b j| ≤ θ / ((1 - δ - θ) * Real.sqrt S) * l2Norm c +
        l2Norm c * (θ / (1 - δ)) * (θ / (1 - δ)) ^ M := by
      intro M
      have := (isClosed_le (hcc j).abs continuous_const).mem_of_tendsto hlim
        (Filter.eventually_atTop.2 ⟨M, fun N hN => by
          have h1 := (hβ (φ N)).2.1 j hj
          have h2 : (θ / (1 - δ)) ^ (φ N) ≤ (θ / (1 - δ)) ^ M :=
            pow_le_pow_of_le_one hr0 hr1.le (hN.trans (hφ.id_le N))
          have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 hr0)
          show |corr X (β (φ N)) j| ≤ θ / ((1 - δ - θ) * Real.sqrt S) * l2Norm c +
            l2Norm c * (θ / (1 - δ)) * (θ / (1 - δ)) ^ M
          linarith⟩)
      exact this
    have ht : Filter.Tendsto (fun M : ℕ => θ / ((1 - δ - θ) * Real.sqrt S) * l2Norm c +
        l2Norm c * (θ / (1 - δ)) * (θ / (1 - δ)) ^ M) Filter.atTop
        (nhds (θ / ((1 - δ - θ) * Real.sqrt S) * l2Norm c + l2Norm c * (θ / (1 - δ)) * 0)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul _).const_add _
    have := le_of_tendsto_of_tendsto' tendsto_const_nhds ht hM
    simpa using this
  · exact (isClosed_le hl2c continuous_const).mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun N => (hβ (φ N)).2.2.1)
  · exact (isClosed_le hl1c continuous_const).mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun N => (hβ (φ N)).2.2.2)


lemma rip_aux_up (A : Set ℝ) (hA : A.Nonempty) (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ s ∈ A, b ≤ (1 + s) * a) : b ≤ (1 + sInf A) * a := by
  have := le_sInf_mul hA ha (t := b - a) fun s hs => by have := h s hs; linarith
  linarith

lemma rip_upper {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (U : Finset (Fin p))
    (hU : U.card ≤ k) (v : Fin p → ℝ) (hv : SupportedOn v U) :
    l2Norm (X.mulVec v) ^ 2 ≤ (1 + restrictedIsometryConst X k) * l2Norm v ^ 2 := by
  have hM := frob_nonneg X
  unfold restrictedIsometryConst
  apply rip_aux_up
  · refine ⟨∑ i, ∑ j, X i j ^ 2 + 1, by linarith, fun T _ c _ => ⟨?_, ?_⟩⟩
    · have := sq_nonneg (l2Norm c); have := sq_nonneg (l2Norm (X.mulVec c)); nlinarith
    · have := frob X c; have := sq_nonneg (l2Norm c); nlinarith
  · exact sq_nonneg _
  · intro s hs
    exact (hs.2 U hU v hv).2

lemma block_sq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (U F : Finset (Fin p))
    (hU : U.card ≤ k) (hF : F.card ≤ k) (b : Fin p → ℝ) (hb : SupportedOn b U) :
    ∑ j ∈ F, corr X b j ^ 2 ≤ (1 + restrictedIsometryConst X k) ^ 2 * l2Norm b ^ 2 := by
  classical
  set A := ∑ j ∈ F, corr X b j ^ 2 with hA
  set u : Fin p → ℝ := fun j => if j ∈ F then corr X b j else 0 with hu
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hus : SupportedOn u F := fun j hj => by simp [hu, hj]
  have h1 : ∑ j, u j * corr X b j = A := by
    rw [hA]
    simp only [hu, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : l2Norm u ^ 2 = A := by
    rw [hu, l2Norm_ite, Real.sq_sqrt hA0]
  have h3 : A ≤ l2Norm (X.mulVec u) * l2Norm (X.mulVec b) := by
    rw [← h1, sum_mul_corr]
    exact (le_abs_self _).trans (abs_dot_le _ _)
  have h4 := rip_upper X k F hF u hus
  have h5 := rip_upper X k U hU b hb
  rw [h2] at h4
  have ha := l2Norm_nonneg (X.mulVec u)
  have hb' := l2Norm_nonneg (X.mulVec b)
  have h6 : A ^ 2 ≤ l2Norm (X.mulVec u) ^ 2 * l2Norm (X.mulVec b) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hA0 h3 2
  have h7 : A ^ 2 ≤ ((1 + restrictedIsometryConst X k) * A) *
      ((1 + restrictedIsometryConst X k) * l2Norm b ^ 2) :=
    h6.trans (mul_le_mul h4 h5 (sq_nonneg _) ((sq_nonneg _).trans h4))
  rcases hA0.eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · have : A * A ≤ A * ((1 + restrictedIsometryConst X k) ^ 2 * l2Norm b ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this h0

lemma main3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S) (δ θ : ℝ)
    (hδ0 : 0 ≤ δ) (hθ : 0 ≤ θ) (hδθ : δ + θ < 1)
    (hlow : ∀ (U : Finset (Fin p)) (v : Fin p → ℝ), U.card ≤ 2 * S → SupportedOn v U →
      (1 - δ) * l2Norm v ^ 2 ≤ l2Norm (X.mulVec v) ^ 2)
    (hrop : ∀ (U U' : Finset (Fin p)) (v v' : Fin p → ℝ), Disjoint U U' → U.card ≤ S →
      U'.card ≤ 2 * S → SupportedOn v U → SupportedOn v' U' →
      |(X.mulVec v) ⬝ᵥ (X.mulVec v')| ≤ θ * l2Norm v * l2Norm v')
    (hblk : ∀ (U F : Finset (Fin p)) (b : Fin p → ℝ), U.card ≤ 2 * S → F.card ≤ 2 * S →
      SupportedOn b U → ∑ j ∈ F, corr X b j ^ 2 ≤ (1 + δ) ^ 2 * l2Norm b ^ 2)
    (β : Fin p → ℝ) (T0 : Finset (Fin p)) (hT0 : T0.card ≤ S) (hβ : SupportedOn β T0)
    (lam : ℝ) (hlam : 0 < lam) (hβlam : l2Norm β < lam * Real.sqrt S) :
    ∃ β' β'' : Fin p → ℝ, β = β' + β'' ∧
      l2Norm β' ≤ (1 + δ) / (1 - δ - θ) * l2Norm β ∧
      l1Norm β' ≤ 2 * (1 + δ) / (1 - δ - θ) * (l2Norm β ^ 2 / lam) ∧
      ∀ j : Fin p, |corr X β'' j| < (1 - δ ^ 2) / (1 - δ - θ) * lam := by
  classical
  have hD : 0 < 1 - δ - θ := by linarith
  have hu : 0 < 1 - δ := by linarith
  have hδ1 : 0 < 1 + δ := by linarith
  have hpos : 0 < (1 - δ ^ 2) / (1 - δ - θ) := div_pos (by nlinarith) hD
  have hcoef : 1 + δ ≤ (1 - δ ^ 2) / (1 - δ - θ) := by
    rw [le_div_iff₀ hD]; nlinarith [mul_nonneg hδ0 hθ]
  set s := l2Norm β with hs
  have hs0 : 0 ≤ s := l2Norm_nonneg _
  have hT02 : T0.card ≤ 2 * S := by omega
  have hpt : ∀ j, |corr X β j| ≤ (1 + δ) * s := by
    intro j
    have h := hblk T0 {j} β hT02 (by simp; omega) hβ
    rw [Finset.sum_singleton] at h
    have h' : |corr X β j| ^ 2 ≤ ((1 + δ) * s) ^ 2 := by rw [sq_abs, mul_pow]; exact h
    nlinarith [abs_nonneg (corr X β j), mul_nonneg hδ1.le hs0]
  rcases lt_or_ge s lam with hsl | hsl
  · have e2 : l2Norm (0 : Fin p → ℝ) = 0 := by simp [l2Norm]
    have e1 : l1Norm (0 : Fin p → ℝ) = 0 := by simp [l1Norm]
    refine ⟨0, β, by simp, ?_, ?_, fun j => ?_⟩
    · rw [e2]; exact mul_nonneg (div_nonneg hδ1.le hD.le) hs0
    · rw [e1]
      exact mul_nonneg (div_nonneg (by linarith) hD.le) (div_nonneg (sq_nonneg _) hlam.le)
    · have h1 := hpt j
      have h2 : (1 + δ) * s < (1 + δ) * lam := mul_lt_mul_of_pos_left hsl hδ1
      have h3 : (1 + δ) * lam ≤ (1 - δ ^ 2) / (1 - δ - θ) * lam :=
        mul_le_mul_of_nonneg_right hcoef hlam.le
      linarith
  · have hlam2 : 0 < lam ^ 2 := by positivity
    set x := s ^ 2 / lam ^ 2 with hx
    have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hlam2]; nlinarith
    have hxS : x < S := by
      rw [hx, div_lt_iff₀ hlam2]
      have h1 : s ^ 2 < (lam * √(S : ℝ)) ^ 2 := pow_lt_pow_left₀ hβlam hs0 (by norm_num)
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h1
      linarith
    have hx0 : 0 ≤ x := by linarith
    set S0 := ⌊x⌋₊ + 1 with hS0
    have hS0S : S0 ≤ S := by
      have := (Nat.floor_lt hx0).2 hxS
      omega
    have hxS0 : x < (S0 : ℝ) := by rw [hS0]; push_cast; exact Nat.lt_floor_add_one x
    have hS02 : (S0 : ℝ) ≤ 2 * x := by
      rw [hS0]; push_cast; have := Nat.floor_le hx0; linarith
    have hS01 : 1 ≤ S0 := by omega
    have hS0pos : (0 : ℝ) < S0 := by exact_mod_cast hS01
    have hsq0 : 0 < √(S0 : ℝ) := Real.sqrt_pos.2 hS0pos
    set v := corr X β with hv
    set t := (1 + δ) * s / √(S0 : ℝ) with ht
    have ht0 : 0 ≤ t := div_nonneg (mul_nonneg hδ1.le hs0) hsq0.le
    set Ω := Finset.univ.filter (fun j => t < |v j|) with hΩ
    have hΩc : Ω.card ≤ S0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨F, hFΩ, hFc⟩ := Finset.exists_subset_card_eq (show S0 + 1 ≤ Ω.card by omega)
      have h1 := hblk T0 F β hT02 (by omega) hβ
      have h2 : ∑ j ∈ F, t ^ 2 < ∑ j ∈ F, v j ^ 2 := by
        apply Finset.sum_lt_sum_of_nonempty
        · rw [← Finset.card_pos, hFc]; omega
        · intro j hj
          have hj' := (Finset.mem_filter.1 (hFΩ hj)).2
          rw [← sq_abs (v j)]
          exact pow_lt_pow_left₀ hj' ht0 (by norm_num)
      rw [Finset.sum_const, hFc, nsmul_eq_mul] at h2
      have h3 : t ^ 2 * S0 = (1 + δ) ^ 2 * s ^ 2 := by
        rw [ht, div_pow, mul_pow, Real.sq_sqrt hS0pos.le]; field_simp
      push_cast at h2
      nlinarith [sq_nonneg t]
    set c : Fin p → ℝ := fun j => if j ∈ Ω then v j else 0 with hc
    have hcn : l2Norm c ≤ (1 + δ) * s := by
      rw [hc, l2Norm_ite]
      have h1 := hblk T0 Ω β hT02 (by omega) hβ
      calc √(∑ j ∈ Ω, v j ^ 2) ≤ √((1 + δ) ^ 2 * s ^ 2) := Real.sqrt_le_sqrt h1
        _ = (1 + δ) * s := by rw [← mul_pow, Real.sqrt_sq (mul_nonneg hδ1.le hs0)]
    obtain ⟨γ, hγ1, hγ2, hγ3, hγ4⟩ := main_core X S0 hS01 δ θ hδθ hθ
      (fun U w hU hw => hlow U w (by omega) hw)
      (fun U U' w w' hd hU hU' hw hw' => hrop U U' w w' hd (by omega) (by omega) hw hw')
      Ω hΩc c
    have hDinv : 0 ≤ 1 / (1 - δ - θ) := div_nonneg zero_le_one hD.le
    refine ⟨γ, β - γ, by ext j; simp, ?_, ?_, fun j => ?_⟩
    · calc l2Norm γ ≤ 1 / (1 - δ - θ) * l2Norm c := hγ3
        _ ≤ 1 / (1 - δ - θ) * ((1 + δ) * s) := mul_le_mul_of_nonneg_left hcn hDinv
        _ = (1 + δ) / (1 - δ - θ) * s := by ring
    · have hspos : 0 < s := lt_of_lt_of_le hlam hsl
      have hk : √(2 * (S0 : ℝ)) ≤ 2 * s / lam := by
        have e : (2 * s / lam) ^ 2 = 4 * x := by rw [hx]; field_simp; ring
        calc √(2 * (S0 : ℝ)) ≤ √((2 * s / lam) ^ 2) := Real.sqrt_le_sqrt (by rw [e]; linarith)
          _ = 2 * s / lam := Real.sqrt_sq (by positivity)
      calc l1Norm γ ≤ √(2 * (S0 : ℝ)) / (1 - δ - θ) * l2Norm c := hγ4
        _ ≤ (2 * s / lam) / (1 - δ - θ) * ((1 + δ) * s) :=
          mul_le_mul (div_le_div_of_nonneg_right hk hD.le) hcn (l2Norm_nonneg _)
            (div_nonneg (by positivity) hD.le)
        _ = 2 * (1 + δ) / (1 - δ - θ) * (s ^ 2 / lam) := by field_simp
    · rw [corr_sub, Pi.sub_apply]
      by_cases hj : j ∈ Ω
      · have h1 : corr X γ j = v j := by rw [hγ1 j hj]; simp [hc, hj]
        rw [h1, sub_self, abs_zero]; exact mul_pos hpos hlam
      · have h1 : |v j| ≤ t := by
          have : ¬ (t < |v j|) := fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
          exact not_lt.1 this
        have h2 := hγ2 j hj
        have h3 : θ / ((1 - δ - θ) * √(S0 : ℝ)) * l2Norm c ≤
            θ / ((1 - δ - θ) * √(S0 : ℝ)) * ((1 + δ) * s) :=
          mul_le_mul_of_nonneg_left hcn (div_nonneg hθ (mul_pos hD hsq0).le)
        have h4 : |v j - corr X γ j| ≤ |v j| + |corr X γ j| := abs_sub _ _
        have h5 : t + θ / ((1 - δ - θ) * √(S0 : ℝ)) * ((1 + δ) * s) =
            (1 - δ ^ 2) / (1 - δ - θ) * (s / √(S0 : ℝ)) := by
          rw [ht]; field_simp; ring
        have h6 : s / √(S0 : ℝ) < lam := by
          rw [div_lt_iff₀ hsq0]
          have h8 : s ^ 2 < (lam * √(S0 : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hS0pos.le]
            have := hxS0; rw [hx, div_lt_iff₀ hlam2] at this; linarith
          exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h8
        have h7 := mul_lt_mul_of_pos_left h6 hpos
        linarith

end A3C

open CandesTao.Decoding DantzigSelector.Sparse in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S)
    (hSp : 3 * S ≤ p)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (β : Fin p → ℝ) (hβ : IsSparse β S) (lam : ℝ) (hlam : 0 < lam)
    (hβlam : l2Norm β < lam * Real.sqrt S) :
    ∃ β' β'' : Fin p → ℝ, β = β' + β'' ∧
      l2Norm β' ≤
        (1 + restrictedIsometryConst X (2 * S)) /
          (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
            l2Norm β ∧
      l1Norm β' ≤
        2 * (1 + restrictedIsometryConst X (2 * S)) /
          (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
            (l2Norm β ^ 2 / lam) ∧
      ∀ j : Fin p, |∑ i, X i j * (X.mulVec β'') i| <
        (1 - restrictedIsometryConst X (2 * S) ^ 2) /
          (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
            lam := by
  have hδ0 : 0 ≤ restrictedIsometryConst X (2 * S) := Real.sInf_nonneg fun x hx => hx.1
  have hθ0 : 0 ≤ restrictedOrthogonalityConst X S (2 * S) := Real.sInf_nonneg fun x hx => hx.1
  obtain ⟨T0, hT0, hβT⟩ := hβ
  obtain ⟨β', β'', h1, h2, h3, h4⟩ := A3C.main3 X S hS _ _ hδ0 hθ0 hδθ
    (fun U v hU hv => A3C.rip_lower X (2 * S) U hU v hv)
    (fun U U' v v' hd hU hU' hv hv' => A3C.rop_bound X S (2 * S) U U' hd hU hU' v v' hv hv')
    (fun U F b hU hF hb => A3C.block_sq X (2 * S) U F hU hF b hb)
    β T0 hT0 hβT lam hlam hβlam
  refine ⟨β', β'', h1, h2, h3, fun j => ?_⟩
  convert h4 j using 2
  rw [A3C.corr_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
