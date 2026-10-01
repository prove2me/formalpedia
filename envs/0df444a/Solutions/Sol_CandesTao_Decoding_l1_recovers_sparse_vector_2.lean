-- Prove2me | solution 2 for CandesTao.Decoding.l1_recovers_sparse_vector
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T10:27:38.941084+00:00
-- url     : https://prove2.me/submissions/cdfe6c1a-0fd1-443c-ba19-a0530dd5f2a1

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_CandesTao_Decoding_L1Minimization
import Theorems.Thm_CandesTao_Decoding_theta_le_delta_le_theta_add_max

set_option autoImplicit false
open CandesTao.Decoding
namespace CSRecovery

theorem poly01_extreme {n k : ℕ} (y : Fin n → ℝ)
    (hy : y ∈ ({z : Fin n → ℝ | (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ ∑ j, z j ≤ k}).extremePoints ℝ) :
    ∀ j, y j = 0 ∨ y j = 1 := by
  rw [mem_extremePoints] at hy
  obtain ⟨⟨hb, hsum⟩, hext⟩ := hy
  have key : ∀ d : Fin n → ℝ, d ≠ 0 → (∀ j, 0 ≤ y j + d j ∧ y j + d j ≤ 1) →
      (∀ j, 0 ≤ y j - d j ∧ y j - d j ≤ 1) → ∑ j, (y j + d j) ≤ k →
      ∑ j, (y j - d j) ≤ k → False := by
    intro d hd h1 h2 h3 h4
    have hseg : y ∈ openSegment ℝ (y + d) (y - d) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext j; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hyd := (hext (y + d) ⟨h1, h3⟩ (y - d) ⟨h2, h4⟩ hseg).1
    apply hd
    ext j
    have := congrFun hyd j
    simp only [Pi.add_apply] at this
    simp only [Pi.zero_apply]; linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj0, hj1⟩ := hcon
  have hj0' : 0 < y j := lt_of_le_of_ne (hb j).1 (Ne.symm hj0)
  have hj1' : y j < 1 := lt_of_le_of_ne (hb j).2 hj1
  by_cases hother : ∃ j', j' ≠ j ∧ 0 < y j' ∧ y j' < 1
  · obtain ⟨j', hne, h0', h1'⟩ := hother
    set ε := min (min (y j) (1 - y j)) (min (y j') (1 - y j')) with hε
    have hεpos : 0 < ε := lt_min (lt_min hj0' (by linarith)) (lt_min h0' (by linarith))
    have e1 : ε ≤ y j := le_trans (min_le_left _ _) (min_le_left _ _)
    have e2 : ε ≤ 1 - y j := le_trans (min_le_left _ _) (min_le_right _ _)
    have e3 : ε ≤ y j' := le_trans (min_le_right _ _) (min_le_left _ _)
    have e4 : ε ≤ 1 - y j' := le_trans (min_le_right _ _) (min_le_right _ _)
    set d : Fin n → ℝ := fun i => (if i = j then ε else 0) - (if i = j' then ε else 0) with hd
    have hdsum : ∑ i, d i = 0 := by
      simp only [hd, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]; ring
    have hcoord : ∀ i, (d i = ε ∧ i = j) ∨ (d i = -ε ∧ i = j') ∨ (d i = 0 ∧ i ≠ j ∧ i ≠ j') := by
      intro i
      by_cases h1 : i = j
      · subst h1; left; simp [hd, hne.symm]
      · by_cases h2 : i = j'
        · subst h2; right; left; simp [hd, h1]
        · right; right; simp [hd, h1, h2]
    apply key d
    · intro h0
      have := congrFun h0 j
      simp [hd, hne.symm] at this
      linarith
    · intro i
      rcases hcoord i with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, -, -⟩ <;> rw [h] <;>
        constructor <;> linarith [hb i]
    · intro i
      rcases hcoord i with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, -, -⟩ <;> rw [h] <;>
        constructor <;> linarith [hb i]
    · rw [Finset.sum_add_distrib, hdsum]; linarith
    · rw [Finset.sum_sub_distrib, hdsum]; linarith
  · push Not at hother
    have hbin : ∀ i, i ≠ j → y i = 0 ∨ y i = 1 := by
      intro i hi
      by_cases h0 : y i = 0
      · left; exact h0
      · right
        have : 0 < y i := lt_of_le_of_ne (hb i).1 (Ne.symm h0)
        exact le_antisymm (hb i).2 (hother i hi this)
    rcases lt_or_eq_of_le hsum with hlt | heq
    · set ε := min (min (y j) (1 - y j)) ((k : ℝ) - ∑ i, y i) with hε
      have hεpos : 0 < ε := lt_min (lt_min hj0' (by linarith)) (by linarith)
      have e1 : ε ≤ y j := le_trans (min_le_left _ _) (min_le_left _ _)
      have e2 : ε ≤ 1 - y j := le_trans (min_le_left _ _) (min_le_right _ _)
      have e3 : ε ≤ (k : ℝ) - ∑ i, y i := min_le_right _ _
      set d : Fin n → ℝ := fun i => if i = j then ε else 0 with hd
      have hdsum : ∑ i, d i = ε := by simp [hd]
      apply key d
      · intro h0
        have := congrFun h0 j
        simp [hd] at this
        linarith
      · intro i
        by_cases h : i = j
        · subst h; simp only [hd, if_true]; constructor <;> linarith
        · simp only [hd, if_neg h]; constructor <;> linarith [hb i]
      · intro i
        by_cases h : i = j
        · subst h; simp only [hd, if_true]; constructor <;> linarith
        · simp only [hd, if_neg h]; constructor <;> linarith [hb i]
      · rw [Finset.sum_add_distrib, hdsum]; linarith
      · rw [Finset.sum_sub_distrib, hdsum]; linarith
    · have hsplit : ∑ i, y i = y j + ∑ i ∈ Finset.univ.erase j, y i := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hcount : ∑ i ∈ Finset.univ.erase j, y i =
          (((Finset.univ.erase j).filter (fun i => y i = 1)).card : ℝ) := by
        rw [← Finset.sum_boole]
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        rcases hbin i hij with h | h
        · rw [h, if_neg (by norm_num)]
        · rw [h, if_pos rfl]
      set M := ((Finset.univ.erase j).filter (fun i => y i = 1)).card
      have hyj : y j = (k : ℝ) - M := by linarith
      have hMk : (M : ℝ) < k := by linarith
      have hkM : (k : ℝ) < M + 1 := by linarith
      have hMk' : M < k := by exact_mod_cast hMk
      have hkM' : k < M + 1 := by exact_mod_cast hkM
      omega

theorem poly01 {n k : ℕ} (c : Fin n → ℝ) (h0 : ∀ j, 0 ≤ c j) (h1 : ∀ j, c j ≤ 1)
    (hs : ∑ j, c j ≤ k) :
    ∃ (F : Finset (Fin n → ℝ)) (w : (Fin n → ℝ) → ℝ), (∀ y ∈ F, 0 ≤ w y) ∧
      ∑ y ∈ F, w y = 1 ∧ ∑ y ∈ F, w y • y = c ∧
      ∀ y ∈ F, (∀ j, y j = 0 ∨ y j = 1) ∧ ∑ j, y j ≤ k := by
  set Q : Set (Fin n → ℝ) := {z | (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ ∑ j, z j ≤ k} with hQ
  set E : Set (Fin n → ℝ) := {z | (∀ j, z j = 0 ∨ z j = 1) ∧ ∑ j, z j ≤ k} with hE
  have hEfin : E.Finite := by
    apply Set.Finite.subset (Set.Finite.pi' (t := fun _ => ({0, 1} : Set ℝ))
      (fun _ => Set.toFinite _))
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hz.1
  have hQc : IsClosed Q := by
    have : Q = (⋂ j, {z : Fin n → ℝ | 0 ≤ z j}) ∩ (⋂ j, {z : Fin n → ℝ | z j ≤ 1}) ∩
        {z | ∑ j, z j ≤ (k : ℝ)} := by
      ext z; simp [hQ, forall_and]
    rw [this]
    exact ((isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_iInter fun j => isClosed_le (continuous_apply j) continuous_const)).inter
      (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)
  have hQcomp : IsCompact Q :=
    (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 1)).of_isClosed_subset hQc
      (fun z hz => ⟨fun j => (hz.1 j).1, fun j => (hz.1 j).2⟩)
  have hQconv : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun j => ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx.1 j, hy.1 j]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx.1 j, hy.1 j]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      nlinarith [hx.2, hy.2]
  have hKM := closure_convexHull_extremePoints hQcomp hQconv
  have hcQ : c ∈ Q := ⟨fun j => ⟨h0 j, h1 j⟩, hs⟩
  have hextE : Q.extremePoints ℝ ⊆ E := by
    intro y hy
    exact ⟨poly01_extreme y hy, (extremePoints_subset hy).2⟩
  have hsub : Q ⊆ convexHull ℝ E := by
    rw [← hKM]
    have hcl : IsClosed (convexHull ℝ E) := (hEfin.isCompact_convexHull (𝕜 := ℝ)).isClosed
    exact closure_minimal (convexHull_mono hextE) hcl
  have hcE := hsub hcQ
  have hEeq : E = ((hEfin.toFinset : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by simp
  rw [hEeq, Finset.mem_convexHull'] at hcE
  obtain ⟨w, hw0, hw1, hwc⟩ := hcE
  refine ⟨hEfin.toFinset, w, hw0, hw1, hwc, ?_⟩
  intro y hy
  rw [Set.Finite.mem_toFinset] at hy
  exact hy


/-- The set whose infimum is `δ_k`. -/
def DS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : Set ℝ :=
  {δ : ℝ | 0 ≤ δ ∧ ∀ T : Finset (Fin m), T.card ≤ k → ∀ c : Fin m → ℝ, SupportedOn c T →
    (1 - δ) * l2Norm c ^ 2 ≤ l2Norm (F.mulVec c) ^ 2 ∧
    l2Norm (F.mulVec c) ^ 2 ≤ (1 + δ) * l2Norm c ^ 2}

/-- The set whose infimum is `θ_{k,k'}`. -/
def TS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) : Set ℝ :=
  {θ : ℝ | 0 ≤ θ ∧ ∀ T T' : Finset (Fin m), Disjoint T T' → T.card ≤ k → T'.card ≤ k' →
    ∀ c c' : Fin m → ℝ, SupportedOn c T → SupportedOn c' T' →
    |dotProduct (F.mulVec c) (F.mulVec c')| ≤ θ * l2Norm c * l2Norm c'}

lemma nsq {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

lemma nsq_add {n : ℕ} (x y : Fin n → ℝ) :
    l2Norm (x + y) ^ 2 = l2Norm x ^ 2 + 2 * dotProduct x y + l2Norm y ^ 2 := by
  rw [nsq, nsq, nsq, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

lemma nsq_sub {n : ℕ} (x y : Fin n → ℝ) :
    l2Norm (x - y) ^ 2 = l2Norm x ^ 2 - 2 * dotProduct x y + l2Norm y ^ 2 := by
  rw [nsq, nsq, nsq, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  ring

lemma nsq_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : l2Norm (a • x) ^ 2 = a ^ 2 * l2Norm x ^ 2 := by
  rw [nsq, nsq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma eq_zero_of_nsq {n : ℕ} (x : Fin n → ℝ) (h : l2Norm x = 0) : x = 0 := by
  have h2 : ∑ i, x i ^ 2 = 0 := by rw [← nsq, h]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))] at h2
  funext i
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h2 i (Finset.mem_univ i))

lemma dot_disjoint {m : ℕ} (c c' : Fin m → ℝ) (T T' : Finset (Fin m)) (hTT : Disjoint T T')
    (hc : SupportedOn c T) (hc' : SupportedOn c' T') : dotProduct c c' = 0 := by
  unfold dotProduct
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ∈ T
  · have : j ∉ T' := Finset.disjoint_left.mp hTT hj
    rw [hc' j this, mul_zero]
  · rw [hc j hj, zero_mul]

lemma supp_add {m : ℕ} (c c' : Fin m → ℝ) (T T' : Finset (Fin m))
    (hc : SupportedOn c T) (hc' : SupportedOn c' T') : SupportedOn (c + c') (T ∪ T') := by
  intro j hj
  rw [Finset.mem_union, not_or] at hj
  simp [hc j hj.1, hc' j hj.2]

lemma supp_sub {m : ℕ} (c c' : Fin m → ℝ) (T T' : Finset (Fin m))
    (hc : SupportedOn c T) (hc' : SupportedOn c' T') : SupportedOn (c - c') (T ∪ T') := by
  intro j hj
  rw [Finset.mem_union, not_or] at hj
  simp [hc j hj.1, hc' j hj.2]

lemma supp_smul {m : ℕ} (a : ℝ) (c : Fin m → ℝ) (T : Finset (Fin m))
    (hc : SupportedOn c T) : SupportedOn (a • c) T := by
  intro j hj
  simp [hc j hj]

/-- Cauchy–Schwarz row by row: `‖F x‖² ≤ (∑ᵢⱼ Fᵢⱼ²) ‖x‖²`. -/
lemma mulVec_sq_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * l2Norm x ^ 2 := by
  rw [nsq, nsq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma DS_nonempty {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : (DS F k).Nonempty := by
  refine ⟨max 1 (∑ i, ∑ j, F i j ^ 2), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro U _ x _
  have h0 : 0 ≤ l2Norm x ^ 2 := sq_nonneg _
  have h1 : 0 ≤ l2Norm (F.mulVec x) ^ 2 := sq_nonneg _
  have hb := mulVec_sq_le F x
  have hm1 : 1 ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_left _ _
  have hmK : (∑ i, ∑ j, F i j ^ 2) ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_right _ _
  constructor
  · nlinarith
  · nlinarith

lemma DS_bdd {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : BddBelow (DS F k) :=
  ⟨0, fun _ hx => hx.1⟩

lemma TS_bdd {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) : BddBelow (TS F k k') :=
  ⟨0, fun _ hx => hx.1⟩

/-- Polarization: an admissible `δ` for `S + S'` is an admissible `θ` for `S, S'`. -/
lemma DS_sub_TS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ) :
    DS F (S + S') ⊆ TS F S S' := by
  intro δ hδ
  refine ⟨hδ.1, ?_⟩
  intro T T' hTT hT hT' c c' hc hc'
  set a := l2Norm c with ha
  set b := l2Norm c' with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  set X := dotProduct (F.mulVec c) (F.mulVec c') with hX
  -- degenerate cases
  by_cases hab : a * b = 0
  · rcases mul_eq_zero.mp hab with h | h
    · have : c = 0 := eq_zero_of_nsq c h
      rw [hX, this, Matrix.mulVec_zero, zero_dotProduct, abs_zero]
      exact mul_nonneg (mul_nonneg hδ.1 ha0) hb0
    · have : c' = 0 := eq_zero_of_nsq c' h
      rw [hX, this, Matrix.mulVec_zero, dotProduct_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hδ.1 ha0) hb0
  have habpos : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha0 hb0) (Ne.symm hab)
  -- rescaled vectors
  set u := b • c with hu
  set v := a • c' with hv
  have hcard : (T ∪ T').card ≤ S + S' := by
    rw [Finset.card_union_of_disjoint hTT]; omega
  have hsu := supp_smul b c T hc
  have hsv := supp_smul a c' T' hc'
  have huv0 : dotProduct u v = 0 := dot_disjoint u v T T' hTT hsu hsv
  have hnu : l2Norm u ^ 2 = b ^ 2 * a ^ 2 := by rw [hu, nsq_smul]
  have hnv : l2Norm v ^ 2 = a ^ 2 * b ^ 2 := by rw [hv, nsq_smul]
  have hp := (hδ.2 _ hcard (u + v) (supp_add u v T T' hsu hsv)).2
  have hm := (hδ.2 _ hcard (u - v) (supp_sub u v T T' hsu hsv)).1
  rw [nsq_add, huv0, hnu, hnv] at hp
  rw [nsq_sub, huv0, hnu, hnv] at hm
  have hp2 := (hδ.2 _ hcard (u + v) (supp_add u v T T' hsu hsv)).1
  have hm2 := (hδ.2 _ hcard (u - v) (supp_sub u v T T' hsu hsv)).2
  rw [nsq_add, huv0, hnu, hnv] at hp2
  rw [nsq_sub, huv0, hnu, hnv] at hm2
  rw [Matrix.mulVec_add, nsq_add] at hp hp2
  rw [Matrix.mulVec_sub, nsq_sub] at hm hm2
  have hFuv : dotProduct (F.mulVec u) (F.mulVec v) = a * b * X := by
    rw [hu, hv, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, hX]
    ring
  rw [hFuv] at hp hm hp2 hm2
  -- `4 a b X ≤ 4 δ a² b²` and `-4 δ a² b² ≤ 4 a b X`
  have hup : a * b * X ≤ δ * (a * b) * (a * b) := by nlinarith
  have hlo : -(δ * (a * b) * (a * b)) ≤ a * b * X := by nlinarith
  rw [abs_le]
  constructor
  · have := (mul_le_mul_iff_of_pos_left habpos).mp (by nlinarith : a * b * (-(δ * a * b)) ≤ a * b * X)
    linarith
  · have := (mul_le_mul_iff_of_pos_left habpos).mp (by nlinarith : a * b * X ≤ a * b * (δ * a * b))
    linarith



/-- Strict null-space property from the concrete RIP and orthogonality bounds. -/
theorem nullspace_concrete {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ)
    (S : ℕ) (hS : 1 ≤ S) (δ θ : ℝ) (hδ : δ ∈ DS F (2 * S))
    (hθ : θ ∈ TS F S (2 * S)) (hgap : δ + θ < 1)
    (T : Finset (Fin m)) (hT : T.card ≤ S) (h : Fin m → ℝ)
    (hhkernel : F.mulVec h = 0) (hhne : h ≠ 0) :
    (∑ j ∈ T, |h j|) < ∑ j ∈ Tᶜ, |h j| := by
  classical
  by_contra hnsp
  set L := ∑ j ∈ T, |h j| with hLdef
  set V := ∑ j ∈ Tᶜ, |h j| with hVdef
  have hVL : V ≤ L := not_lt.mp hnsp
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hL : L ≠ 0 := by
    intro hLz
    have hV0 : V = 0 := le_antisymm (hLz ▸ hVL)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hhead := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)).1 hLz
    have htail := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)).1 hV0
    apply hhne
    funext j
    by_cases hj : j ∈ T
    · exact abs_eq_zero.1 (hhead j hj)
    · exact abs_eq_zero.1 (htail j (Finset.mem_compl.2 hj))
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
  have hSr : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  -- threshold
  set a : ℝ := L / S with hadef
  have hapos : 0 < a := by positivity
  have hSa : (S : ℝ) * a = L := by rw [hadef]; field_simp
  set T1 : Finset (Fin m) := Tᶜ.filter (fun j => a < |h j|) with hT1def
  set R : Finset (Fin m) := Tᶜ.filter (fun j => ¬ a < |h j|) with hRdef
  set k1 : ℕ := T1.card with hk1def
  have hsplitV : ∑ j ∈ T1, |h j| + ∑ j ∈ R, |h j| = V :=
    Finset.sum_filter_add_sum_filter_not Tᶜ _ _
  have hk1a : (k1 : ℝ) * a ≤ ∑ j ∈ T1, |h j| := by
    have := Finset.card_nsmul_le_sum T1 (fun j => |h j|) a
      (fun j hj => le_of_lt (Finset.mem_filter.1 hj).2)
    simpa [nsmul_eq_mul] using this
  have hRnn : 0 ≤ ∑ j ∈ R, |h j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hk1S : k1 ≤ S := by
    have : (k1 : ℝ) * a ≤ S * a := by linarith
    have := le_of_mul_le_mul_right this hapos
    exact_mod_cast this
  have hRsum : ∑ j ∈ R, |h j| ≤ ((S - k1 : ℕ) : ℝ) * a := by
    rw [Nat.cast_sub hk1S]
    nlinarith
  have hRle : ∀ j ∈ R, |h j| ≤ a := fun j hj => not_lt.1 (Finset.mem_filter.1 hj).2
  have hRT : ∀ j ∈ R, j ∉ T := fun j hj => Finset.mem_compl.1 (Finset.mem_filter.1 hj).1
  -- card of Rᶜ
  have hcardR : Rᶜ.card = T.card + k1 := by
    have c1 := Finset.card_filter_add_card_filter_not (s := Tᶜ) (fun j => a < |h j|)
    have c2 := Finset.card_compl R
    have c3 := Finset.card_compl T
    have c4 : T.card ≤ Fintype.card (Fin m) := Finset.card_le_univ T
    have c5 : R.card ≤ Fintype.card (Fin m) := Finset.card_le_univ R
    rw [← hT1def, ← hRdef] at c1
    omega
  -- normalized vector c
  set c : Fin m → ℝ := fun j => if j ∈ R then |h j| / a else 0 with hcdef
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j; by_cases hj : j ∈ R
    · simp only [hcdef, if_pos hj]; positivity
    · simp [hcdef, hj]
  have hc1 : ∀ j, c j ≤ 1 := by
    intro j; by_cases hj : j ∈ R
    · simp only [hcdef, if_pos hj]; rw [div_le_one hapos]; exact hRle j hj
    · simp [hcdef, hj]
  have hcsum : ∑ j, c j ≤ ((S - k1 : ℕ) : ℝ) := by
    have : ∑ j, c j = (∑ j ∈ R, |h j|) / a := by
      rw [hcdef, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
    rw [this, div_le_iff₀ hapos]
    exact hRsum
  obtain ⟨B, w, hw0, hw1, hwc, hF⟩ := poly01 c hc0 hc1 hcsum
  -- signs
  set g : Fin m → ℝ := fun j => if j ∈ R then a * h j / |h j| else 0 with hgdef
  set v' : Fin m → ℝ := fun j => if j ∈ R then h j else 0 with hv'def
  set H : Fin m → ℝ := fun j => if j ∈ R then 0 else h j with hHdef
  have hgc : ∀ j, c j * g j = v' j := by
    intro j
    by_cases hj : j ∈ R
    · simp only [hcdef, hgdef, hv'def, if_pos hj]
      by_cases h0 : h j = 0
      · simp [h0]
      · have : |h j| ≠ 0 := abs_ne_zero.2 h0
        field_simp
    · simp [hcdef, hgdef, hv'def, hj]
  set u : (Fin m → ℝ) → (Fin m → ℝ) := fun y j => y j * g j with hudef
  have hcoord : ∀ j, ∑ y ∈ B, w y * y j = c j := by
    intro j
    have := congrFun hwc j
    rw [Finset.sum_apply] at this
    simpa using this
  have hv'eq : ∑ y ∈ B, w y • u y = v' := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hudef]
    rw [← hgc j, ← hcoord j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _; ring
  have hhHv : h = H + v' := by
    funext j
    by_cases hj : j ∈ R <;> simp [hHdef, hv'def, hj]
  have hFHtail : F.mulVec H = -(∑ y ∈ B, w y • F.mulVec (u y)) := by
    have : F.mulVec H + F.mulVec v' = 0 := by rw [← Matrix.mulVec_add, ← hhHv, hhkernel]
    rw [← hv'eq, Matrix.mulVec_sum] at this
    simp only [Matrix.mulVec_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  have hcardy : ∀ y ∈ B, (Finset.univ.filter (fun j => y j ≠ 0)).card ≤ S - k1 := by
    intro y hy
    obtain ⟨h01, hsum⟩ := hF y hy
    have : ∑ j, y j = ((Finset.univ.filter (fun j => y j ≠ 0)).card : ℝ) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro j _
      rcases h01 j with h | h
      · simp [h]
      · simp [h]
    rw [this] at hsum
    exact_mod_cast hsum

  have hHsupp : SupportedOn H Rᶜ := by
    intro j hj
    simp [hHdef, Finset.notMem_compl.1 hj]
  have hHcard : Rᶜ.card ≤ 2 * S := by rw [hcardR]; omega
  have hCS : L ^ 2 ≤ (S : ℝ) * l2Norm H ^ 2 := by
    have hhead : ∑ j ∈ T, h j ^ 2 = ∑ j ∈ T, H j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjR : j ∉ R := fun hRj => (hRT j hRj) hj
      simp [hHdef, hjR]
    have hsum : ∑ j ∈ T, H j ^ 2 ≤ l2Norm H ^ 2 := by
      rw [nsq]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        (fun j _ _ => sq_nonneg (H j))
    have hcard : (T.card : ℝ) ≤ S := by exact_mod_cast hT
    calc
      L ^ 2 ≤ (T.card : ℝ) * ∑ j ∈ T, h j ^ 2 := by
        simpa [L, sq_abs] using (sq_sum_le_card_mul_sum_sq (s := T) (f := fun j => |h j|))
      _ ≤ (S : ℝ) * ∑ j ∈ T, H j ^ 2 := by
        rw [hhead]
        exact mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun j _ => sq_nonneg _)
      _ ≤ (S : ℝ) * l2Norm H ^ 2 := mul_le_mul_of_nonneg_left hsum hSr.le
  have hHpos : 0 < l2Norm H := by
    have hn : 0 ≤ l2Norm H := Real.sqrt_nonneg _
    by_contra hnot
    have hz : l2Norm H = 0 := le_antisymm (not_lt.mp hnot) hn
    rw [hz] at hCS
    nlinarith
  have hscale : (S : ℝ) * a ^ 2 ≤ l2Norm H ^ 2 := by
    have hSasq : L ^ 2 = (S : ℝ) ^ 2 * a ^ 2 := by rw [← hSa]; ring
    rw [hSasq] at hCS
    apply (mul_le_mul_iff_of_pos_left hSr).mp
    nlinarith only [hCS]
  have hgabs : ∀ j, g j ^ 2 ≤ a ^ 2 := by
    intro j
    by_cases hj : j ∈ R
    · simp only [hgdef, if_pos hj]
      by_cases hzero : h j = 0
      · simp [hzero, sq_nonneg a]
      · have habs : |h j| ≠ 0 := abs_ne_zero.mpr hzero
        apply le_of_eq
        field_simp
        rw [sq_abs]
    · simp [hgdef, hj, sq_nonneg a]
  have hunorm : ∀ y ∈ B, l2Norm (u y) ≤ l2Norm H := by
    intro y hy
    have huy : l2Norm (u y) ^ 2 ≤ (S : ℝ) * a ^ 2 := by
      rw [nsq]
      calc
        ∑ j, u y j ^ 2 ≤ ∑ j, y j * a ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          rcases (hF y hy).1 j with hj | hj <;> simp only [hudef, hj]
          · simp
          · simpa using hgabs j
        _ = (∑ j, y j) * a ^ 2 := (Finset.sum_mul _ _ _).symm
        _ ≤ ((S - k1 : ℕ) : ℝ) * a ^ 2 :=
          mul_le_mul_of_nonneg_right (hF y hy).2 (sq_nonneg a)
        _ ≤ (S : ℝ) * a ^ 2 := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Nat.sub_le S k1)) (sq_nonneg a)
    have hn : 0 ≤ l2Norm (u y) := Real.sqrt_nonneg _
    nlinarith [hscale]
  have hcross : ∀ y ∈ B,
      |dotProduct (F.mulVec (u y)) (F.mulVec H)| ≤ θ * l2Norm H ^ 2 := by
    intro y hy
    let U : Finset (Fin m) := (Finset.univ.filter (fun j => y j ≠ 0)) ∩ R
    have hUcard : U.card ≤ S := le_trans
      (Finset.card_le_card Finset.inter_subset_left) (le_trans (hcardy y hy) (Nat.sub_le _ _))
    have hUsupp : SupportedOn (u y) U := by
      intro j hj
      by_cases hjR : j ∈ R
      · have hyj : y j = 0 := by
          by_contra hneq
          exact hj (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩, hjR⟩)
        simp [hudef, hyj]
      · simp [hudef, hgdef, hjR]
    have hdis : Disjoint U Rᶜ := Finset.disjoint_left.mpr (by
      intro j hj hj'
      exact (Finset.mem_compl.mp hj') (Finset.mem_inter.mp hj).2)
    calc
      |dotProduct (F.mulVec (u y)) (F.mulVec H)| ≤ θ * l2Norm (u y) * l2Norm H :=
        hθ.2 U Rᶜ hdis hUcard hHcard (u y) H hUsupp hHsupp
      _ ≤ θ * l2Norm H * l2Norm H := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hunorm y hy) hθ.1) hHpos.le
      _ = θ * l2Norm H ^ 2 := by ring
  have hFinner : l2Norm (F.mulVec H) ^ 2 =
      -(∑ y ∈ B, w y * dotProduct (F.mulVec (u y)) (F.mulVec H)) := by
    have hid : l2Norm (F.mulVec H) ^ 2 = dotProduct (F.mulVec H) (F.mulVec H) := by
      rw [nsq, dotProduct]
      apply Finset.sum_congr rfl
      intro j _; ring
    rw [hid]
    conv_lhs => lhs; rw [hFHtail]
    rw [neg_dotProduct, sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have hFupper : l2Norm (F.mulVec H) ^ 2 ≤ θ * l2Norm H ^ 2 := by
    rw [hFinner, ← Finset.sum_neg_distrib]
    calc
      ∑ y ∈ B, -(w y * dotProduct (F.mulVec (u y)) (F.mulVec H)) ≤
          ∑ y ∈ B, w y * (θ * l2Norm H ^ 2) := by
        apply Finset.sum_le_sum
        intro y hy
        have hb : -dotProduct (F.mulVec (u y)) (F.mulVec H) ≤ θ * l2Norm H ^ 2 :=
          le_trans (neg_le_abs _) (hcross y hy)
        have hb' := mul_le_mul_of_nonneg_left hb (hw0 y hy)
        nlinarith only [hb']
      _ = θ * l2Norm H ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]
  have hFlower := (hδ.2 Rᶜ hHcard H hHsupp).1
  have hHsqpos : 0 < l2Norm H ^ 2 := sq_pos_of_pos hHpos
  have hstrict := mul_lt_mul_of_pos_right hgap hHsqpos
  nlinarith only [hFlower, hFupper, hstrict]

end CSRecovery

open CSRecovery in
theorem solution {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 3 * S ≤ m)
    (h : restrictedIsometryConst F S + restrictedOrthogonalityConst F S S +
      restrictedOrthogonalityConst F S (2 * S) < 1)
    (T : Finset (Fin m)) (c : Fin m → ℝ) (hT : T.card ≤ S) (hc : SupportedOn c T) :
    IsUniqueL1Minimizer F (F.mulVec c) c := by
  classical
  have hdelta := (theta_le_delta_le_theta_add_max F S S hS hS (by omega)).2
  have h2S : S + S = 2 * S := by omega
  rw [h2S, max_self] at hdelta
  have hgap : restrictedIsometryConst F (2 * S) +
      restrictedOrthogonalityConst F S (2 * S) < 1 := by linarith
  set ε := (1 - restrictedIsometryConst F (2 * S) -
      restrictedOrthogonalityConst F S (2 * S)) / 3 with hε
  have hεpos : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨δ, hδ, hδlt⟩ := exists_lt_of_csInf_lt (DS_nonempty F (2 * S))
    (by change restrictedIsometryConst F (2 * S) < restrictedIsometryConst F (2 * S) + ε
        linarith)
  have hTne : (TS F S (2 * S)).Nonempty :=
    (DS_nonempty F (S + 2 * S)).mono (DS_sub_TS F S (2 * S))
  obtain ⟨θ, hθ, hθlt⟩ := exists_lt_of_csInf_lt hTne
    (by change restrictedOrthogonalityConst F S (2 * S) <
          restrictedOrthogonalityConst F S (2 * S) + ε
        linarith)
  change δ < restrictedIsometryConst F (2 * S) + ε at hδlt
  change θ < restrictedOrthogonalityConst F S (2 * S) + ε at hθlt
  have hconcrete : δ + θ < 1 := by dsimp [ε] at hδlt hθlt; linarith
  refine ⟨rfl, ?_⟩
  intro d hd hdne
  have hker : F.mulVec (d - c) = 0 := by rw [Matrix.mulVec_sub, hd, sub_self]
  have hne : d - c ≠ 0 := by
    intro hz
    exact hdne (sub_eq_zero.mp hz)
  have hNSP := nullspace_concrete F S hS δ θ hδ hθ hconcrete T hT (d - c) hker hne
  have htail : ∑ j ∈ Tᶜ, |(d - c) j| = ∑ j ∈ Tᶜ, |d j| := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [hc j (Finset.mem_compl.mp hj)]
  rw [htail] at hNSP
  have hhead : ∑ j ∈ T, |c j| ≤ ∑ j ∈ T, |d j| + ∑ j ∈ T, |(d - c) j| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hb := abs_add_le (d j) (c j - d j)
    rw [add_sub_cancel, abs_sub_comm] at hb
    simpa using hb
  have hcnorm : l1Norm c = ∑ j ∈ T, |c j| := by
    unfold l1Norm
    rw [← Finset.sum_add_sum_compl T (fun j => |c j|)]
    have hz : ∑ j ∈ Tᶜ, |c j| = 0 := Finset.sum_eq_zero (fun j hj => by
      rw [hc j (Finset.mem_compl.mp hj), abs_zero])
    rw [hz, add_zero]
  have hdnorm : l1Norm d = ∑ j ∈ T, |d j| + ∑ j ∈ Tᶜ, |d j| := by
    exact (Finset.sum_add_sum_compl T (fun j => |d j|)).symm
  rw [hcnorm, hdnorm]
  linarith
