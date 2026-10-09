-- Prove2me | solution 1 for DantzigSelector.Oracle.dantzig_oracle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T20:56:37.495986+00:00
-- url     : https://prove2.me/submissions/848b2899-7eb2-44d5-b9a6-52eb3c64cb3f

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
theorem A3C.corA3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S)
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

namespace DS7

open DantzigSelector.Oracle

lemma ric_mono {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) {k K : ℕ} (hkK : k ≤ K) :
    restrictedIsometryConst X k ≤ restrictedIsometryConst X K := by
  have hM := DS6.frob_nonneg X
  unfold restrictedIsometryConst
  apply csInf_le_csInf ⟨0, fun _ hx => hx.1⟩
  · refine ⟨∑ i, ∑ j, X i j ^ 2 + 1, by linarith, fun T _ c _ => ⟨?_, ?_⟩⟩
    · have := sq_nonneg (l2Norm c); have := sq_nonneg (l2Norm (X.mulVec c)); nlinarith
    · have := DS6.frob X c; have := sq_nonneg (l2Norm c); nlinarith
  · intro s hs
    exact ⟨hs.1, fun T hT c hc => hs.2 T (hT.trans hkK) c hc⟩

lemma roc_mono {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) {k k' K K' : ℕ} (hk : k ≤ K)
    (hk' : k' ≤ K') :
    restrictedOrthogonalityConst X k k' ≤ restrictedOrthogonalityConst X K K' := by
  have hM := DS6.frob_nonneg X
  unfold restrictedOrthogonalityConst
  apply csInf_le_csInf ⟨0, fun _ hx => hx.1⟩
  · refine ⟨∑ i, ∑ j, X i j ^ 2, hM, fun T T' _ _ _ c c' _ _ => ?_⟩
    calc |(X.mulVec c) ⬝ᵥ (X.mulVec c')| ≤ l2Norm (X.mulVec c) * l2Norm (X.mulVec c') :=
          DS6.abs_dot_le _ _
      _ ≤ (√(∑ i, ∑ j, X i j ^ 2) * l2Norm c) * (√(∑ i, ∑ j, X i j ^ 2) * l2Norm c') :=
          mul_le_mul (DS6.norm_mulVec_le X c) (DS6.norm_mulVec_le X c') (DS6.l2Norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (DS6.l2Norm_nonneg _))
      _ = (√(∑ i, ∑ j, X i j ^ 2) * √(∑ i, ∑ j, X i j ^ 2)) * l2Norm c * l2Norm c' := by ring
      _ = (∑ i, ∑ j, X i j ^ 2) * l2Norm c * l2Norm c' := by rw [Real.mul_self_sqrt hM]
  · intro s hs
    exact ⟨hs.1, fun T T' hd hT hT' c c' hc hc' =>
      hs.2 T T' hd (hT.trans hk) (hT'.trans hk') c c' hc hc'⟩

/-- cone constraint with a perturbation `β'`. -/
lemma cone2 {p : ℕ} (βI β' h : Fin p → ℝ) (T0 : Finset (Fin p))
    (hβ : SupportedOn βI T0) (hle : l1Norm (βI + β' + h) ≤ l1Norm (βI + β')) :
    l1On h T0ᶜ ≤ l1On h T0 + 2 * l1Norm β' := by
  classical
  unfold l1Norm at hle ⊢
  unfold l1On
  have hs1 : ∑ j ∈ T0, (|(βI + β') j| - |(βI + β' + h) j|) ≤ ∑ j ∈ T0, |h j| :=
    Finset.sum_le_sum fun j _ => by
      have := abs_add_le ((βI + β' + h) j) (-(h j))
      have e : (βI + β' + h) j + -h j = (βI + β') j := by simp only [Pi.add_apply]; ring
      rw [e, abs_neg] at this
      linarith
  have hs2 : ∑ j ∈ T0ᶜ, (|(βI + β') j| - |(βI + β' + h) j|) ≤
      ∑ j ∈ T0ᶜ, (2 * |β' j| - |h j|) :=
    Finset.sum_le_sum fun j hj => by
      have h0 : βI j = 0 := hβ j (Finset.mem_compl.mp hj)
      simp only [Pi.add_apply, h0, zero_add]
      have := abs_add_le (β' j + h j) (-(β' j))
      have e : β' j + h j + -β' j = h j := by ring
      rw [e, abs_neg] at this
      linarith
  have htot : 0 ≤ ∑ j, (|(βI + β') j| - |(βI + β' + h) j|) := by
    rw [Finset.sum_sub_distrib]; linarith
  rw [← Finset.sum_add_sum_compl T0] at htot
  have h3 : ∑ j ∈ T0ᶜ, (2 * |β' j| - |h j|) = 2 * ∑ j ∈ T0ᶜ, |β' j| - ∑ j ∈ T0ᶜ, |h j| := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have h4 : ∑ j ∈ T0ᶜ, |β' j| ≤ ∑ j, |β' j| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
  linarith

lemma L_gt_one (p : ℕ) (hp : 3 ≤ p) : 1 < Real.sqrt (2 * Real.log p) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : 1 < Real.log p := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < 2 * Real.log p by linarith)
  rwa [Real.sqrt_one] at this

set_option maxHeartbeats 1000000 in
/-- Theorem 1.1-type estimate at block size `k ≤ S` with the constants `δ_{2S}`, `θ_{S,2S}`. -/
lemma core {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S k : ℕ) (hk : 1 ≤ k) (hkS : k ≤ S)
    (hSp : 3 * S ≤ p)
    (hRIP : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (T0 : Finset (Fin p)) (hT0 : T0.card = k) (h : Fin p → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (htube : ∀ j : Fin p, |∑ i, X i j * X.mulVec h i| ≤ 2 * r)
    (E : ℝ) (hE : 0 ≤ E) (hcone : l1On h T0ᶜ ≤ l1On h T0 + E) :
    ∃ A : ℝ, 0 ≤ A ∧
      (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) * A ≤
        2 * r * √(2 * (k : ℝ)) + restrictedOrthogonalityConst X S (2 * S) * (E / √(k : ℝ)) ∧
      l2Norm h ≤ 2 * A + E / √(k : ℝ) := by
  classical
  have hδk := ric_mono X (show 2 * k ≤ 2 * S by omega)
  have hθk := roc_mono X hkS (show 2 * k ≤ 2 * S by omega)
  have hθk0 : 0 ≤ restrictedOrthogonalityConst X k (2 * k) := DS6.roc_nonneg X k (2 * k)
  have hRIPk : restrictedIsometryConst X (2 * k) + restrictedOrthogonalityConst X k (2 * k) < 1 := by
    linarith
  have hcc : k ≤ T0ᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨T1, hT1sub, hT1c, hT1top⟩ := DS6.top_exists h T0ᶜ k hcc
  have hTB : IsTopBlock h T0 T1 k := ⟨hT1sub, hT1c, hT1top⟩
  obtain ⟨hA, hB⟩ := DS6.lemma31 X hk hRIPk T0 T1 hT0 h hTB
  have hdisj : Disjoint T0 T1 := by
    rw [Finset.disjoint_left]; intro j hj0 hj1; exact (Finset.mem_compl.1 (hT1sub hj1)) hj0
  have hcardU : (T0 ∪ T1).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hdisj, hT0, hT1c]; ring
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsp : 0 < √(k : ℝ) := Real.sqrt_pos.2 hkpos
  set Q := Real.sqrt (∑ j ∈ T0 ∪ T1, (∑ i, X i j * X.mulVec h i) ^ 2) with hQdef
  have hQ : Q ≤ 2 * r * √(2 * (k : ℝ)) := by
    have : ∑ j ∈ T0 ∪ T1, (∑ i, X i j * X.mulVec h i) ^ 2 ≤ ∑ j ∈ T0 ∪ T1, (2 * r) ^ 2 :=
      Finset.sum_le_sum fun j _ => by
        have := htube j; have := abs_nonneg (∑ i, X i j * X.mulVec h i)
        have := sq_abs (∑ i, X i j * X.mulVec h i); nlinarith
    rw [Finset.sum_const, hcardU, nsmul_eq_mul] at this
    calc Q ≤ √(((2 * k : ℕ) : ℝ) * (2 * r) ^ 2) := Real.sqrt_le_sqrt this
      _ = 2 * r * √(2 * (k : ℝ)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]; push_cast; ring
  set x := l2On h (T0 ∪ T1) with hx
  set Lh := l1On h T0ᶜ with hLdef
  have hx0 : 0 ≤ x := DS6.l2On_nonneg h _
  have hL0 : 0 ≤ Lh := DS6.l1On_nonneg h _
  have hLx : Lh ≤ √(k : ℝ) * x + E := by
    have h1 := DS6.l1_le_sqrt_card h T0
    rw [hT0] at h1
    have h2 : l2On h T0 ≤ x := DS6.l2On_mono h Finset.subset_union_left
    have h3 := mul_le_mul_of_nonneg_left h2 hsp.le
    linarith
  set δk := restrictedIsometryConst X (2 * k) with hδkdef
  set θk := restrictedOrthogonalityConst X k (2 * k) with hθkdef
  have hu : 0 < 1 - δk := by linarith
  have e2 : (1 - δk) * x ≤ Q + θk * (Lh / √(k : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hA hu.le
    have e : (1 - δk) * (1 / (1 - δk) * Q + θk / ((1 - δk) * √(k : ℝ)) * Lh)
        = Q + θk * (Lh / √(k : ℝ)) := by
      field_simp
    linarith
  have hLk : Lh / √(k : ℝ) ≤ x + E / √(k : ℝ) := by
    have := div_le_div_of_nonneg_right hLx hsp.le
    have e : (√(k : ℝ) * x + E) / √(k : ℝ) = x + E / √(k : ℝ) := by
      field_simp
    linarith
  have hF0 : 0 ≤ E / √(k : ℝ) := div_nonneg hE hsp.le
  have hLk0 : 0 ≤ Lh / √(k : ℝ) := div_nonneg hL0 hsp.le
  have e3 : (1 - δk - θk) * x ≤ Q + θk * (E / √(k : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hLk hθk0]
  refine ⟨x, hx0, ?_, ?_⟩
  · have h1 : (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) * x
        ≤ (1 - δk - θk) * x := mul_le_mul_of_nonneg_right (by linarith) hx0
    have h2 : θk * (E / √(k : ℝ)) ≤ restrictedOrthogonalityConst X S (2 * S) * (E / √(k : ℝ)) :=
      mul_le_mul_of_nonneg_right hθk hF0
    linarith
  · have hL2 : (k : ℝ)⁻¹ * Lh ^ 2 = (Lh / √(k : ℝ)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hkpos.le]; ring
    have h2 : l2Norm h ^ 2 ≤ (2 * x + E / √(k : ℝ)) ^ 2 := by
      nlinarith [mul_self_le_mul_self hLk0 hLk]
    have hn := DS6.l2Norm_nonneg h
    nlinarith

/-- the final coefficient comparison. -/
lemma coefU (δ θ lam C0v u : ℝ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1 + δ) (hu1 : 1 ≤ (1 + δ) * u)
    (hu : 0 < u) (hlam : 2 ≤ lam) (hC0 : 2 * √2 * (2 + δ) + (1 + δ) ^ 2 * u ≤ C0v) :
    4 * √2 * lam * u + 8 * θ * (1 + δ) * u ^ 2 + 5 * ((1 + δ) * u) + 1 ≤
      (2 * C0v * u + 2 * θ * (1 + δ) * u ^ 2 + (1 + δ) * u) * lam := by
  have hs2 : 1 ≤ √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hZ : 0 ≤ 2 * (C0v - 2 * √2) * u + 2 * θ * (1 + δ) * u ^ 2 + (1 + δ) * u := by
    have : 0 ≤ C0v - 2 * √2 := by nlinarith [sq_nonneg (1 + δ)]
    positivity
  have H1 := mul_nonneg (sub_nonneg.2 hlam) hZ
  have H2 : 0 ≤ u * (C0v - (2 * √2 * (2 + δ) + (1 + δ) ^ 2 * u)) :=
    mul_nonneg hu.le (sub_nonneg.2 hC0)
  have H3 : 0 ≤ (√2 - 1) * ((1 + δ) * u) := mul_nonneg (by linarith) (by positivity)
  have H4 : 0 ≤ (1 + δ - θ) * (1 + δ) * u * u := by
    have : 0 ≤ 1 + δ - θ := by linarith
    positivity
  nlinarith [H1, H2, H3, H4, hu1]

lemma assemble (δ θ lam A F s R W N : ℝ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hD : 0 < 1 - δ - θ)
    (hlam : 2 ≤ lam) (hA0 : 0 ≤ A) (hF0 : 0 ≤ F) (hs0 : 0 ≤ s) (hW : W ≤ R) (hsR : s ≤ R)
    (hDA : (1 - δ - θ) * A ≤ 2 * √2 * lam * W + θ * F)
    (hF : F ≤ 4 * ((1 + δ) / (1 - δ - θ)) * s)
    (hN : N ≤ 2 * A + F + s + (1 + δ) / (1 - δ - θ) * s) :
    N ≤ C2 δ θ * lam * R := by
  set D := 1 - δ - θ with hDdef
  set u := 1 / D with hudef
  have hu : 0 < u := by positivity
  have huD : u * D = 1 := by rw [hudef]; field_simp
  have hKu : (1 + δ) / D = (1 + δ) * u := by rw [hudef]; ring
  rw [hKu] at hF hN
  have hu1 : 1 ≤ (1 + δ) * u := by
    rw [← hKu, le_div_iff₀ hD]; linarith
  have hR0 : 0 ≤ R := le_trans hs0 hsR
  have hC0 : 2 * √2 * (2 + δ) + (1 + δ) ^ 2 * u ≤ C0 δ θ := by
    unfold C0
    have hq : 1 + δ ≤ (1 - δ ^ 2) / D := by
      rw [le_div_iff₀ hD]; nlinarith
    have e : (1 + 1 / √2) * (1 + δ) ^ 2 / (1 - δ - θ) = (1 + δ) ^ 2 * u + 1 / √2 * ((1 + δ) ^ 2 * u) := by
      rw [hudef]; ring
    rw [e]
    have : 0 ≤ 1 / √2 * ((1 + δ) ^ 2 * u) := by positivity
    have h2 : 0 ≤ 2 * √2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hq h2]
  have hC2 : C2 δ θ = 2 * C0 δ θ * u + 2 * θ * (1 + δ) * u ^ 2 + (1 + δ) * u := by
    have e : C2 δ θ = 2 * C0 δ θ / D + 2 * θ * (1 + δ) / D ^ 2 + (1 + δ) / D := rfl
    rw [e, hudef]; ring
  have hcoef := coefU δ θ lam (C0 δ θ) u hδ hθ (by linarith) hu1 hu hlam hC0
  rw [hC2]
  have hAu : A ≤ u * (2 * √2 * lam * W + θ * F) := by
    have := mul_le_mul_of_nonneg_left hDA hu.le
    rwa [← mul_assoc, huD, one_mul] at this
  have hs2 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have g1 : u * (2 * √2 * lam * W) ≤ u * (2 * √2 * lam * R) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (by positivity)) hu.le
  have hFR : F ≤ 4 * ((1 + δ) * u) * R :=
    le_trans hF (mul_le_mul_of_nonneg_left hsR (by positivity))
  have g2 : u * (θ * F) ≤ u * (θ * (4 * ((1 + δ) * u) * R)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFR hθ) hu.le
  have g3 : (1 + δ) * u * s ≤ (1 + δ) * u * R := mul_le_mul_of_nonneg_left hsR (by positivity)
  have g4 := mul_le_mul_of_nonneg_right hcoef hR0
  nlinarith [g1, g2, g3, g4, hAu, hFR]

set_option maxHeartbeats 1000000 in
/-- the deterministic oracle inequality on the noise event. -/
theorem oracle {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (S : ℕ) (hS : 1 ≤ S) (hSp : 3 * S ≤ p) (σ : ℝ) (hσ : 0 < σ)
    (β : Fin p → ℝ) (hβ : IsSparse β S) (t : ℝ) (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1 - t)
    (L : ℝ) (hL1 : 1 < L) (z : Fin n → ℝ)
    (hz : ∀ j, |∑ i, X i j * z i| ≤ Real.sqrt (1 + a) * L * σ)
    (b : Fin p → ℝ)
    (hb : IsDantzigSelector X (X.mulVec β + z) ((Real.sqrt (1 + a) + t⁻¹) * L * σ) b) :
    l2Norm (b - β) ^ 2 ≤
      C2 (restrictedIsometryConst X (2 * S)) (restrictedOrthogonalityConst X S (2 * S)) ^ 2 *
        ((Real.sqrt (1 + a) + t⁻¹) * L) ^ 2 * (σ ^ 2 + idealMSE β σ) := by
  classical
  have hδ0 : 0 ≤ restrictedIsometryConst X (2 * S) := DS6.ric_nonneg X (2 * S)
  have hθ0 : 0 ≤ restrictedOrthogonalityConst X S (2 * S) := DS6.roc_nonneg X S (2 * S)
  set δ := restrictedIsometryConst X (2 * S) with hδdef
  set θ := restrictedOrthogonalityConst X S (2 * S) with hθdef
  have hDpos : 0 < 1 - δ - θ := by linarith
  have ht1 : t < 1 := by linarith
  have hsa : 1 ≤ Real.sqrt (1 + a) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + a by linarith)
    rwa [Real.sqrt_one] at this
  have htinv : 1 ≤ t⁻¹ := by
    have := mul_inv_cancel₀ ht.ne'
    nlinarith only [this, mul_nonneg (inv_nonneg.2 ht.le) (sub_nonneg.2 ht1.le)]
  set lam := (Real.sqrt (1 + a) + t⁻¹) * L with hlamdef
  have hlam2 : 2 ≤ lam := by
    rw [hlamdef]
    nlinarith only [hsa, htinv, hL1,
      mul_nonneg (show 0 ≤ Real.sqrt (1 + a) + t⁻¹ by linarith) (sub_nonneg.2 hL1.le)]
  have hlamσ : 0 ≤ lam * σ := by positivity
  -- split β at the noise level
  obtain ⟨T, hTc, hTs⟩ := hβ
  set I := Finset.univ.filter (fun i => σ < |β i|) with hI
  have hIT : I ⊆ T := fun i hi => by
    by_contra hn
    have h0 := hTs i hn
    have := (Finset.mem_filter.1 hi).2
    rw [h0, abs_zero] at this
    linarith
  set βI := DS6.rs β I with hβIdef
  set βc := DS6.rs β Iᶜ with hβcdef
  have hβsplit : β = βI + βc := by
    funext j
    simp only [hβIdef, hβcdef, DS6.rs, Pi.add_apply, Finset.mem_compl]
    by_cases hj : j ∈ I <;> simp [hj]
  set m := I.card with hmdef
  set s := l2Norm βc with hsdef
  have hs0 : 0 ≤ s := DS6.l2Norm_nonneg _
  have hs2 : s ^ 2 = ∑ j ∈ Iᶜ, β j ^ 2 := by
    rw [hsdef, hβcdef, DS6.l2Norm_rs]; unfold l2On
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hle_sig : ∀ j ∈ Iᶜ, β j ^ 2 ≤ σ ^ 2 := fun j hj => by
    have h1 : ¬ σ < |β j| := fun h =>
      (Finset.mem_compl.1 hj) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    have h2 := not_lt.1 h1
    nlinarith only [h2, sq_abs (β j), abs_nonneg (β j), hσ]
  have hmse : idealMSE β σ = m * σ ^ 2 + s ^ 2 := by
    unfold idealMSE
    rw [← Finset.sum_add_sum_compl I (fun j => min (β j ^ 2) (σ ^ 2)), hs2]
    have h1 : ∑ j ∈ I, min (β j ^ 2) (σ ^ 2) = ∑ j ∈ I, σ ^ 2 :=
      Finset.sum_congr rfl fun j hj => by
        have : σ < |β j| := (Finset.mem_filter.1 hj).2
        apply min_eq_right
        nlinarith only [this, sq_abs (β j), hσ]
    have h2 : ∑ j ∈ Iᶜ, min (β j ^ 2) (σ ^ 2) = ∑ j ∈ Iᶜ, β j ^ 2 :=
      Finset.sum_congr rfl fun j hj => min_eq_left (hle_sig j hj)
    rw [h1, h2, Finset.sum_const, nsmul_eq_mul]
  have hsum_eq : ∑ j ∈ Iᶜ, β j ^ 2 = ∑ j ∈ T \ I, β j ^ 2 := by
    symm
    apply Finset.sum_subset
    · intro j hj; exact Finset.mem_compl.2 (Finset.mem_sdiff.1 hj).2
    · intro j hj hn
      have : j ∉ T := fun hT => hn (Finset.mem_sdiff.2 ⟨hT, Finset.mem_compl.1 hj⟩)
      simp [hTs j this]
  have hTI : (T \ I).card + m = T.card := Finset.card_sdiff_add_card_eq_card hIT
  have hmS : m + (T \ I).card ≤ S := by omega
  have hsS : s ^ 2 ≤ ((S - m : ℕ) : ℝ) * σ ^ 2 := by
    have h1 : s ^ 2 ≤ ((T \ I).card : ℝ) * σ ^ 2 := by
      rw [hs2, hsum_eq]
      calc ∑ j ∈ T \ I, β j ^ 2 ≤ ∑ j ∈ T \ I, σ ^ 2 :=
            Finset.sum_le_sum fun j hj =>
              hle_sig j (Finset.mem_compl.2 (Finset.mem_sdiff.1 hj).2)
        _ = ((T \ I).card : ℝ) * σ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ((T \ I).card : ℝ) ≤ ((S - m : ℕ) : ℝ) := by exact_mod_cast (by omega)
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (sq_nonneg σ))
  -- the block size k
  have hσ2 : 0 < σ ^ 2 := by positivity
  set x := s ^ 2 / σ ^ 2 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxs : s ^ 2 = x * σ ^ 2 := by rw [hxdef]; field_simp
  have hxS : x ≤ ((S - m : ℕ) : ℝ) := by rw [hxdef, div_le_iff₀ hσ2]; exact hsS
  set c := ⌈x⌉₊ with hc
  have hcS : c ≤ S - m := Nat.ceil_le.2 hxS
  have hxc : x ≤ c := Nat.le_ceil x
  have hcx : (c : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  set k := max 1 (m + c) with hk
  have hk1 : 1 ≤ k := le_max_left _ _
  have hkS : k ≤ S := max_le hS (by omega)
  have hmk : m ≤ k := le_trans (Nat.le_add_right m c) (le_max_right _ _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hkx : x ≤ k := by
    have h1 : m + c ≤ k := le_max_right _ _
    have h2 : ((m + c : ℕ) : ℝ) ≤ k := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hkR : (k : ℝ) ≤ m + 1 + x := by
    rcases le_total 1 (m + c) with h | h
    · rw [hk, max_eq_right h]; push_cast; linarith
    · rw [hk, max_eq_left h]; push_cast; linarith
  have hsk : s ^ 2 ≤ k * σ ^ 2 := by rw [hxs]; exact mul_le_mul_of_nonneg_right hkx hσ2.le
  have hkR' : (k : ℝ) * σ ^ 2 ≤ σ ^ 2 + idealMSE β σ := by
    rw [hmse, hxs]
    have := mul_le_mul_of_nonneg_right hkR hσ2.le
    linarith only [this]
  -- Corollary A.3 on βc at level μ = L σ
  set μ := L * σ with hμdef
  have hμ : 0 < μ := by positivity
  have hβc_sp : IsSparse βc S := ⟨T, hTc, fun j hj => by simp [hβcdef, DS6.rs, hTs j hj]⟩
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hβc_lt : l2Norm βc < μ * √(S : ℝ) := by
    rw [← hsdef]
    have h3 : ((S - m : ℕ) : ℝ) ≤ S := by exact_mod_cast Nat.sub_le S m
    have h3' : s ^ 2 ≤ S * σ ^ 2 := le_trans hsS (mul_le_mul_of_nonneg_right h3 hσ2.le)
    have h4 : 1 < L ^ 2 := by nlinarith only [hL1]
    have h2 : (μ * √(S : ℝ)) ^ 2 = L ^ 2 * σ ^ 2 * S := by
      rw [mul_pow, Real.sq_sqrt hSpos.le, hμdef]; ring
    have h5 : S * σ ^ 2 < (μ * √(S : ℝ)) ^ 2 := by
      rw [h2]; have := mul_pos hσ2 hSpos; nlinarith only [this, h4]
    by_contra hcon
    have hcon' := not_lt.1 hcon
    have h1 := mul_self_le_mul_self (by positivity) hcon'
    nlinarith only [h1, h3', h5]
  obtain ⟨β', β'', hsplit, hβ'2, hβ'1, hβ''⟩ :=
    A3C.corA3 X S hS hSp (by linarith) βc hβc_sp μ hμ hβc_lt
  -- the competitor βI + β' is feasible
  have hy : X.mulVec β + z = X.mulVec (βI + β') + (X.mulVec β'' + z) := by
    have : X.mulVec β = X.mulVec (βI + β') + X.mulVec β'' := by
      rw [← Matrix.mulVec_add]; congr 1; rw [hβsplit, hsplit]; abel
    rw [this]; abel
  have h3 : (1 - δ ^ 2) / (1 - δ - θ) * μ ≤ t⁻¹ * L * σ := by
    have h1 : (1 - δ ^ 2) / (1 - δ - θ) ≤ t⁻¹ := by
      rw [div_le_iff₀ hDpos]
      have := inv_mul_cancel₀ ht.ne'
      have h2 := mul_le_mul_of_nonneg_left (show t ≤ 1 - δ - θ by linarith) (inv_nonneg.2 ht.le)
      nlinarith only [this, h2, sq_nonneg δ]
    have := mul_le_mul_of_nonneg_right h1 hμ.le
    rw [hμdef] at this ⊢
    linarith [show t⁻¹ * (L * σ) = t⁻¹ * L * σ by ring]
  have hz' : ∀ j, |∑ i, X i j * (X.mulVec β'' + z) i| ≤ lam * σ := by
    intro j
    have e : ∑ i, X i j * (X.mulVec β'' + z) i
        = ∑ i, X i j * X.mulVec β'' i + ∑ i, X i j * z i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
    rw [e]
    have h1 := hβ'' j
    have h2 := hz j
    calc |∑ i, X i j * X.mulVec β'' i + ∑ i, X i j * z i|
        ≤ |∑ i, X i j * X.mulVec β'' i| + |∑ i, X i j * z i| := abs_add_le _ _
      _ ≤ t⁻¹ * L * σ + Real.sqrt (1 + a) * L * σ := by linarith
      _ = lam * σ := by rw [hlamdef]; ring
  have hfeasT : DantzigFeasible X (X.mulVec β + z) (lam * σ) (βI + β') := by
    intro j
    rw [hy]
    have : ∀ i, (X.mulVec (βI + β') + (X.mulVec β'' + z)) i - X.mulVec (βI + β') i
        = (X.mulVec β'' + z) i := fun i => by simp
    simp only [this]
    exact hz' j
  have htube := DS6.tube X (βI + β') b (X.mulVec β'' + z) (lam * σ) hz'
    (by rw [← hy]; exact hb.1)
  set h := b - (βI + β') with hhdef
  have hle : l1Norm (βI + β' + h) ≤ l1Norm (βI + β') := by
    have : βI + β' + h = b := by rw [hhdef]; abel
    rw [this]; exact hb.2 _ hfeasT
  obtain ⟨T0, hIT0, -, hT0c⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ I) hmk
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hβI0 : SupportedOn βI T0 := fun j hj => by
    have : j ∉ I := fun h => hj (hIT0 h)
    simp [hβIdef, DS6.rs, this]
  have hcone := cone2 βI β' h T0 hβI0 hle
  have hE0 : 0 ≤ 2 * l1Norm β' := by
    unfold l1Norm; positivity
  obtain ⟨A, hA0, hDA, hhA⟩ := core X S k hk1 hkS hSp (by linarith) T0 hT0c h (lam * σ) hlamσ
    htube (2 * l1Norm β') hE0 hcone
  -- scalar facts
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hsp : 0 < √(k : ℝ) := Real.sqrt_pos.2 hkpos
  set R := Real.sqrt (σ ^ 2 + idealMSE β σ) with hRdef
  have hMSE0 : 0 ≤ σ ^ 2 + idealMSE β σ := by
    rw [hmse]
    have h1 : (0 : ℝ) ≤ m * σ ^ 2 := mul_nonneg hm0 (sq_nonneg σ)
    have h2 := sq_nonneg σ
    have h3 := sq_nonneg s
    linarith only [h1, h2, h3]
  have hRsq : R ^ 2 = σ ^ 2 + idealMSE β σ := Real.sq_sqrt hMSE0
  have hWk : √(k : ℝ) * σ = Real.sqrt ((k : ℝ) * σ ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hσ.le]
  have hW : √(k : ℝ) * σ ≤ R := by rw [hWk]; exact Real.sqrt_le_sqrt hkR'
  have hsR : s ≤ R := by
    rw [← Real.sqrt_sq hs0]; exact Real.sqrt_le_sqrt (by rw [hmse]; nlinarith)
  have hsW : s ≤ √(k : ℝ) * σ := by
    rw [hWk, ← Real.sqrt_sq hs0]; exact Real.sqrt_le_sqrt hsk
  have hDA' : (1 - δ - θ) * A ≤ 2 * √2 * lam * (√(k : ℝ) * σ) + θ * (2 * l1Norm β' / √(k : ℝ)) := by
    have e : 2 * (lam * σ) * √(2 * (k : ℝ)) = 2 * √2 * lam * (√(k : ℝ) * σ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rw [← e]; exact hDA
  have hF : 2 * l1Norm β' / √(k : ℝ) ≤ 4 * ((1 + δ) / (1 - δ - θ)) * s := by
    have h1 : s ^ 2 / μ ≤ s * √(k : ℝ) := by
      rw [div_le_iff₀ hμ]
      have e1 : s ^ 2 ≤ s * (√(k : ℝ) * σ) := by nlinarith only [mul_le_mul_of_nonneg_left hsW hs0]
      have hpos : 0 ≤ s * √(k : ℝ) * σ := by positivity
      have e2 : s * (√(k : ℝ) * σ) ≤ s * √(k : ℝ) * μ := by
        rw [hμdef]; nlinarith only [mul_nonneg hpos (sub_nonneg.2 hL1.le)]
      linarith
    have hK0 : 0 ≤ 2 * (1 + δ) / (1 - δ - θ) := by positivity
    have h2 : l1Norm β' ≤ 2 * (1 + δ) / (1 - δ - θ) * (s * √(k : ℝ)) :=
      le_trans hβ'1 (mul_le_mul_of_nonneg_left h1 hK0)
    rw [div_le_iff₀ hsp]
    have e : 2 * (2 * (1 + δ) / (1 - δ - θ) * (s * √(k : ℝ)))
        = 4 * ((1 + δ) / (1 - δ - θ)) * s * √(k : ℝ) := by ring
    linarith
  have hβ''eq : β'' = βc - β' := by rw [hsplit]; abel
  have hbb : b - β = h - β'' := by
    rw [hhdef]
    conv_lhs => rw [hβsplit, hsplit]
    abel
  have hN : l2Norm (b - β) ≤ 2 * A + 2 * l1Norm β' / √(k : ℝ) + s + (1 + δ) / (1 - δ - θ) * s := by
    rw [hbb]
    have h1 := A3C.l2Norm_sub_le h β''
    have h2 : l2Norm β'' ≤ s + l2Norm β' := by rw [hβ''eq]; exact A3C.l2Norm_sub_le βc β'
    linarith
  have hF0 : 0 ≤ 2 * l1Norm β' / √(k : ℝ) := div_nonneg hE0 hsp.le
  have hfin := assemble δ θ lam A (2 * l1Norm β' / √(k : ℝ)) s R (√(k : ℝ) * σ)
    (l2Norm (b - β)) hδ0 hθ0 hDpos hlam2 hA0 hF0 hs0 hW hsR hDA' hF hN
  have hn0 := DS6.l2Norm_nonneg (b - β)
  have hsq := mul_self_le_mul_self hn0 hfin
  rw [← hRsq]
  nlinarith only [hsq]

end DS7

open MeasureTheory ProbabilityTheory CandesTao.Decoding DantzigSelector.Sparse DantzigSelector.Oracle in
theorem solution {n p : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitNormColumns X)
    (S : ℕ) (hS : 1 ≤ S) (hSp : 3 * S ≤ p) (σ : ℝ) (hσ : 0 < σ)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) P)
    (hind : iIndepFun z P) (β : Fin p → ℝ) (hβ : IsSparse β S) (t : ℝ) (ht : 0 < t)
    (a : ℝ) (ha : 0 ≤ a)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1 - t) :
    P {ω | ¬ ((∃ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                ((Real.sqrt (1 + a) + t⁻¹) * Real.sqrt (2 * Real.log p) * σ) b) ∧
            ∀ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                ((Real.sqrt (1 + a) + t⁻¹) * Real.sqrt (2 * Real.log p) * σ) b →
              l2Norm (b - β) ^ 2 ≤
                C2 (restrictedIsometryConst X (2 * S)) (restrictedOrthogonalityConst X S (2 * S)) ^ 2 *
                  ((Real.sqrt (1 + a) + t⁻¹) * Real.sqrt (2 * Real.log p)) ^ 2 *
                  (σ ^ 2 + idealMSE β σ))} <
      ENNReal.ofReal (1 / (Real.sqrt (Real.pi * Real.log p) * (p : ℝ) ^ a)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hfin := DS6.final_ineq p (by omega) a ha
  have hL1 : 1 < Real.sqrt (2 * Real.log p) := DS7.L_gt_one p (by omega)
  have huL : Real.sqrt (1 + a) * Real.sqrt (2 * Real.log p) = Real.sqrt (2 * (1 + a) * Real.log p) := by
    rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
  set u := Real.sqrt (2 * (1 + a) * Real.log p) with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 (by positivity)
  set L := Real.sqrt (2 * Real.log p) with hL
  set w : Fin n → Ω → ℝ := fun i ω => σ⁻¹ * z i ω with hw
  have hwlaw : ∀ i, HasLaw (w i) (gaussianReal 0 1) P := by
    intro i
    have h := gaussianReal_const_mul (hz i) σ⁻¹
    rw [mul_zero] at h
    convert h using 2
    apply NNReal.eq
    show (1 : ℝ) = σ⁻¹ ^ 2 * σ ^ 2
    field_simp
  have hwind : iIndepFun w P := hind.comp (fun i x => σ⁻¹ * x) (fun i => by fun_prop)
  have hsub : {ω | ¬ ((∃ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                ((Real.sqrt (1 + a) + t⁻¹) * L * σ) b) ∧
            ∀ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                ((Real.sqrt (1 + a) + t⁻¹) * L * σ) b →
              l2Norm (b - β) ^ 2 ≤
                C2 (restrictedIsometryConst X (2 * S)) (restrictedOrthogonalityConst X S (2 * S)) ^ 2 *
                  ((Real.sqrt (1 + a) + t⁻¹) * L) ^ 2 *
                  (σ ^ 2 + idealMSE β σ))} ⊆
      {ω | ∃ j : Fin p, u < |∑ i, X i j * w i ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hc
    simp only [not_exists, not_lt] at hc
    apply hω
    have hzj : ∀ j : Fin p, |∑ i, X i j * z i ω| ≤ Real.sqrt (1 + a) * L * σ := by
      intro j
      have e : ∑ i, X i j * z i ω = σ * ∑ i, X i j * w i ω := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show X i j * z i ω = σ * (X i j * (σ⁻¹ * z i ω))
        field_simp
      rw [e, abs_mul, abs_of_pos hσ, huL]
      have := mul_le_mul_of_nonneg_left (hc j) hσ.le
      linarith
    have hfeas : DantzigFeasible X (X.mulVec β + fun i => z i ω)
        ((Real.sqrt (1 + a) + t⁻¹) * L * σ) β := by
      intro j
      have : ∀ i, (X.mulVec β + fun i => z i ω) i - X.mulVec β i = z i ω := fun i => by simp
      simp only [this]
      have h1 := hzj j
      have h2 : 0 ≤ t⁻¹ * L * σ := by
        have : 0 < L := by linarith
        positivity
      linarith [show (Real.sqrt (1 + a) + t⁻¹) * L * σ = Real.sqrt (1 + a) * L * σ + t⁻¹ * L * σ by ring]
    exact ⟨DS6.exists_ds X _ _ β hfeas, fun b hb =>
      DS7.oracle X S hS hSp σ hσ β hβ t ht a ha hδθ L hL1 (fun i => z i ω) hzj b hb⟩
  have hmt := DS6.max_tail_strict P (by omega) X hX w hwlaw hwind u hu0
  exact lt_of_le_of_lt (measure_mono hsub) (hmt.trans_le (ENNReal.ofReal_le_ofReal hfin))
