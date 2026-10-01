-- Prove2me | solution 1 for CandesTao.Decoding.dual_reconstruction_l2
-- status  : ACCEPTED   (prove)
-- author  : @radokirov
-- created : 2026-10-01T05:20:04.139177+00:00
-- url     : https://prove2.me/submissions/99612fb1-e5f6-42b6-b94e-b7062486d1b1

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

open CandesTao.Decoding

namespace CandesTaoLemma21

lemma nsq {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

lemma l2_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ l2Norm x := Real.sqrt_nonneg _

lemma eq_zero_of_l2 {n : ℕ} (x : Fin n → ℝ) (h : l2Norm x = 0) : x = 0 := by
  have h2 : ∑ i, x i ^ 2 = 0 := by rw [← nsq, h]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))] at h2
  funext i
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h2 i (Finset.mem_univ i))

lemma dot_self_eq {n : ℕ} (x : Fin n → ℝ) : dotProduct x x = l2Norm x ^ 2 := by
  rw [nsq, dotProduct]; exact Finset.sum_congr rfl fun i _ => by ring

/-- Cauchy–Schwarz for `l2Norm`. -/
lemma abs_dot_le {n : ℕ} (x y : Fin n → ℝ) : |dotProduct x y| ≤ l2Norm x * l2Norm y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have h2 : dotProduct x y ^ 2 ≤ (l2Norm x * l2Norm y) ^ 2 := by
    rw [mul_pow, nsq, nsq]; exact h
  exact abs_le_of_sq_le_sq' h2 (mul_nonneg (l2_nonneg _) (l2_nonneg _)) |> abs_le.mpr

lemma mulVec_sq_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * l2Norm x ^ 2 := by
  rw [nsq, nsq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

def DS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k : ℕ) : Set ℝ :=
  {δ : ℝ | 0 ≤ δ ∧ ∀ T : Finset (Fin m), T.card ≤ k → ∀ c : Fin m → ℝ, SupportedOn c T →
    (1 - δ) * l2Norm c ^ 2 ≤ l2Norm (F.mulVec c) ^ 2 ∧
    l2Norm (F.mulVec c) ^ 2 ≤ (1 + δ) * l2Norm c ^ 2}

def TS {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) : Set ℝ :=
  {θ : ℝ | 0 ≤ θ ∧ ∀ T T' : Finset (Fin m), Disjoint T T' → T.card ≤ k → T'.card ≤ k' →
    ∀ c c' : Fin m → ℝ, SupportedOn c T → SupportedOn c' T' →
    |dotProduct (F.mulVec c) (F.mulVec c')| ≤ θ * l2Norm c * l2Norm c'}

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

lemma norm_mulVec_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ≤ Real.sqrt (∑ i, ∑ j, F i j ^ 2) * l2Norm x := by
  have hK : 0 ≤ ∑ i, ∑ j, F i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_sq (l2_nonneg (F.mulVec x)), ← Real.sqrt_sq (l2_nonneg x),
    ← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt (mulVec_sq_le F x)

lemma TS_nonempty {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (k k' : ℕ) :
    (TS F k k').Nonempty := by
  set K := ∑ i, ∑ j, F i j ^ 2 with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨K, hK, ?_⟩
  intro T T' _ _ _ c c' _ _
  have e1 := norm_mulVec_le F c
  have e2 := norm_mulVec_le F c'
  have hs : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK
  calc |dotProduct (F.mulVec c) (F.mulVec c')|
      ≤ l2Norm (F.mulVec c) * l2Norm (F.mulVec c') := abs_dot_le _ _
    _ ≤ (Real.sqrt K * l2Norm c) * (Real.sqrt K * l2Norm c') :=
        mul_le_mul e1 e2 (l2_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (l2_nonneg _))
    _ = (Real.sqrt K * Real.sqrt K) * l2Norm c * l2Norm c' := by ring
    _ = K * l2Norm c * l2Norm c' := by rw [hs]

/-- The infimum `θ_{S,S'}` itself satisfies the orthogonality inequality. -/
lemma orth_bound {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ)
    (T T' : Finset (Fin m)) (hTT : Disjoint T T') (hT : T.card ≤ S) (hT' : T'.card ≤ S')
    (x y : Fin m → ℝ) (hx : SupportedOn x T) (hy : SupportedOn y T') :
    |dotProduct (F.mulVec x) (F.mulVec y)| ≤
      restrictedOrthogonalityConst F S S' * l2Norm x * l2Norm y := by
  have e : restrictedOrthogonalityConst F S S' = sInf (TS F S S') := rfl
  rw [e]
  by_cases h0 : l2Norm x * l2Norm y = 0
  · rcases mul_eq_zero.mp h0 with h | h
    · rw [eq_zero_of_l2 x h, Matrix.mulVec_zero, zero_dotProduct, abs_zero]
      unfold l2Norm; simp
    · rw [eq_zero_of_l2 y h, Matrix.mulVec_zero, dotProduct_zero, abs_zero]
      unfold l2Norm; simp
  have hpos : 0 < l2Norm x * l2Norm y :=
    lt_of_le_of_ne (mul_nonneg (l2_nonneg _) (l2_nonneg _)) (Ne.symm h0)
  have : |dotProduct (F.mulVec x) (F.mulVec y)| / (l2Norm x * l2Norm y) ≤ sInf (TS F S S') := by
    apply le_csInf (TS_nonempty F S S')
    intro θ hθ
    rw [div_le_iff₀ hpos]
    have := hθ.2 T T' hTT hT hT' x y hx hy
    linarith [this, show θ * l2Norm x * l2Norm y = θ * (l2Norm x * l2Norm y) by ring]
  rw [div_le_iff₀ hpos] at this
  linarith [this, show sInf (TS F S S') * l2Norm x * l2Norm y =
    sInf (TS F S S') * (l2Norm x * l2Norm y) by ring]

/-- The infimum `δ_S` itself satisfies the two isometry inequalities. -/
lemma iso_bounds {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ) (T : Finset (Fin m))
    (hT : T.card ≤ S) (x : Fin m → ℝ) (hx : SupportedOn x T) :
    (1 - restrictedIsometryConst F S) * l2Norm x ^ 2 ≤ l2Norm (F.mulVec x) ^ 2 ∧
    l2Norm (F.mulVec x) ^ 2 ≤ (1 + restrictedIsometryConst F S) * l2Norm x ^ 2 := by
  have e : restrictedIsometryConst F S = sInf (DS F S) := rfl
  rw [e]
  by_cases h0 : l2Norm x = 0
  · rw [h0, eq_zero_of_l2 x h0, Matrix.mulVec_zero]
    have : l2Norm (0 : Fin p → ℝ) = 0 := by unfold l2Norm; simp
    rw [this]; simp
  have hpos : 0 < l2Norm x ^ 2 := by positivity
  set q := l2Norm (F.mulVec x) ^ 2 / l2Norm x ^ 2 with hq
  have hqx : q * l2Norm x ^ 2 = l2Norm (F.mulVec x) ^ 2 := by
    rw [hq]; field_simp
  constructor
  · have : 1 - q ≤ sInf (DS F S) := by
      apply le_csInf (DS_nonempty F S)
      intro δ hδ
      have h := (hδ.2 T hT x hx).1
      rw [← hqx] at h
      nlinarith
    nlinarith
  · have : q - 1 ≤ sInf (DS F S) := by
      apply le_csInf (DS_nonempty F S)
      intro δ hδ
      have h := (hδ.2 T hT x hx).2
      rw [← hqx] at h
      nlinarith
    nlinarith

end CandesTaoLemma21

namespace CandesTaoLemma21

lemma sum_dot_column {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (w : Fin p → ℝ)
    (h : Fin m → ℝ) :
    ∑ j, h j * dotProduct w (column F j) = dotProduct w (F.mulVec h) := by
  simp only [dotProduct, column, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma dot_column_eq {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (w : Fin p → ℝ) (j : Fin m) :
    dotProduct w (column F j) = (F.transpose.mulVec w) j := by
  simp only [dotProduct, column, Matrix.mulVec, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dot_FF {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (u : Fin m → ℝ) :
    dotProduct u (F.transpose.mulVec (F.mulVec u)) = l2Norm (F.mulVec u) ^ 2 := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dot_self_eq]

end CandesTaoLemma21

open CandesTaoLemma21 in
theorem solution :
    ∃ K : ℝ → ℝ, (∀ δ : ℝ, 0 < K δ) ∧
    ∀ {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S S' : ℕ),
      1 ≤ S → 1 ≤ S' → S + S' ≤ m → restrictedIsometryConst F S < 1 →
      ∀ (T : Finset (Fin m)) (c : Fin m → ℝ), T.card ≤ S → SupportedOn c T →
      ∃ w : Fin p → ℝ, w ∈ columnSpan F ∧
        (∀ j ∈ T, dotProduct w (column F j) = c j) ∧
        (∃ E : Finset (Fin m), Disjoint E T ∧ E.card ≤ S' ∧
          (∀ j, j ∉ T → j ∉ E →
            |dotProduct w (column F j)| ≤
              restrictedOrthogonalityConst F S S' /
                ((1 - restrictedIsometryConst F S) * Real.sqrt S') * l2Norm c) ∧
          Real.sqrt (∑ j ∈ E, dotProduct w (column F j) ^ 2) ≤
            restrictedOrthogonalityConst F S S' / (1 - restrictedIsometryConst F S) * l2Norm c) ∧
        l2Norm w ≤ K (restrictedIsometryConst F S) * l2Norm c := by
  refine ⟨fun δ => Real.sqrt (1 + |δ|) / |1 - δ| + 1, fun δ => by positivity, ?_⟩
  intro p m F S S' hS hS' hSS' hδ T c hT hc
  classical
  set δ := restrictedIsometryConst F S with hδdef
  set θ := restrictedOrthogonalityConst F S S' with hθdef
  have hδ0 : 0 ≤ δ := Real.sInf_nonneg fun x hx => hx.1
  have hθ0 : 0 ≤ θ := Real.sInf_nonneg fun x hx => hx.1
  have hpos : 0 < 1 - δ := by linarith
  -- the restricted Gram map `u ↦ (Fᵀ F u)|_T`, completed by the identity off `T`
  let P : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun i => if i ∈ T then LinearMap.proj i else 0)
  let G : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    (Matrix.mulVecLin F.transpose).comp ((Matrix.mulVecLin F).comp P)
  let Φ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun j => if j ∈ T then (LinearMap.proj j).comp G else LinearMap.proj j)
  have hP : ∀ u i, P u i = if i ∈ T then u i else 0 := by
    intro u i; simp only [P, LinearMap.pi_apply]; split_ifs <;> simp
  have hPsupp : ∀ u, SupportedOn u T → P u = u := by
    intro u hu; funext i; rw [hP]; split_ifs with hi
    · rfl
    · exact (hu i hi).symm
  have hΦ : ∀ u j, Φ u j =
      if j ∈ T then (F.transpose.mulVec (F.mulVec (P u))) j else u j := by
    intro u j; simp only [Φ, LinearMap.pi_apply]; split_ifs <;> rfl
  -- injectivity from the lower isometry bound
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hus : SupportedOn u T := by
      intro j hj
      have := congrFun hu j
      rw [hΦ, if_neg hj] at this
      exact this
    have hG : ∀ j ∈ T, (F.transpose.mulVec (F.mulVec u)) j = 0 := by
      intro j hj
      have := congrFun hu j
      rw [hΦ, if_pos hj, hPsupp u hus] at this
      exact this
    have h0 : l2Norm (F.mulVec u) ^ 2 = 0 := by
      rw [← dot_FF, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j ∈ T
      · rw [hG j hj, mul_zero]
      · rw [hus j hj, zero_mul]
    have hb := (iso_bounds F S T hT u hus).1
    rw [← hδdef, h0] at hb
    have : l2Norm u ^ 2 ≤ 0 := by
      by_contra hcon; push Not at hcon
      have := mul_pos hpos hcon; linarith
    exact eq_zero_of_l2 u (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm this (sq_nonneg _)))
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) c
  have hus : SupportedOn u T := by
    intro j hj
    have := congrFun hu j
    rw [hΦ, if_neg hj] at this
    rw [this]; exact hc j hj
  have huT : ∀ j ∈ T, (F.transpose.mulVec (F.mulVec u)) j = c j := by
    intro j hj
    have := congrFun hu j
    rw [hΦ, if_pos hj, hPsupp u hus] at this
    exact this
  set w := F.mulVec u with hwdef
  set a : Fin m → ℝ := fun j => dotProduct w (column F j) with hadef
  have hwT : ∀ j ∈ T, dotProduct w (column F j) = c j := by
    intro j hj; rw [dot_column_eq, hwdef, huT j hj]
  -- size of `u`
  have hFu : l2Norm w ^ 2 = dotProduct u c := by
    rw [hwdef, ← dot_FF, dotProduct, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ T
    · rw [huT j hj]
    · rw [hus j hj, zero_mul, zero_mul]
  have hule : (1 - δ) * l2Norm u ≤ l2Norm c := by
    have hb := (iso_bounds F S T hT u hus).1
    rw [← hδdef, ← hwdef, hFu] at hb
    have hcs := le_trans (le_abs_self _) (abs_dot_le u c)
    by_cases h0 : l2Norm u = 0
    · rw [h0, mul_zero]; exact l2_nonneg _
    have hup : 0 < l2Norm u := lt_of_le_of_ne (l2_nonneg _) (Ne.symm h0)
    have : (1 - δ) * l2Norm u * l2Norm u ≤ l2Norm c * l2Norm u := by nlinarith
    exact le_of_mul_le_mul_right this hup
  have hule' : l2Norm u ≤ l2Norm c / (1 - δ) := by
    rw [le_div_iff₀ hpos]; linarith
  set R := θ / (1 - δ) * l2Norm c with hR
  have hR0 : 0 ≤ R := mul_nonneg (div_nonneg hθ0 hpos.le) (l2_nonneg _)
  -- ℓ² bound on any admissible set off `T`
  have hL2 : ∀ E' : Finset (Fin m), Disjoint E' T → E'.card ≤ S' →
      Real.sqrt (∑ j ∈ E', a j ^ 2) ≤ R := by
    intro E' hdis hcard
    set y : Fin m → ℝ := fun j => if j ∈ E' then a j else 0 with hydef
    have hys : SupportedOn y E' := by intro j hj; simp [hydef, hj]
    have hy2 : ∑ j, y j ^ 2 = ∑ j ∈ E', a j ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ E')]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun j => j ∉ E')) (by
        intro j hj; rw [Finset.mem_filter] at hj; simp [hydef, hj.2]), add_zero]
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.sum_congr rfl fun j hj => by simp [hydef, hj]
    have hyn : l2Norm y = Real.sqrt (∑ j ∈ E', a j ^ 2) := by
      unfold l2Norm; rw [hy2]
    have hya : ∑ j, y j * a j = ∑ j ∈ E', a j ^ 2 := by
      rw [← hy2]; exact Finset.sum_congr rfl fun j _ => by
        simp only [hydef]; split_ifs <;> ring
    have hdot : ∑ j, y j * a j = dotProduct (F.mulVec u) (F.mulVec y) := by
      rw [hadef]; simp only; rw [sum_dot_column]
    have hob := orth_bound F S S' T E' hdis.symm hT hcard u y hus hys
    rw [← hθdef, ← hdot, hya, hyn] at hob
    set s := Real.sqrt (∑ j ∈ E', a j ^ 2) with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hss : s ^ 2 = ∑ j ∈ E', a j ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
    have hsle : s ≤ θ * l2Norm u := by
      by_cases h0 : s = 0
      · rw [h0]; exact mul_nonneg hθ0 (l2_nonneg _)
      have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      rw [← hss, abs_of_nonneg (sq_nonneg _)] at hob
      have : s * s ≤ θ * l2Norm u * s := by nlinarith
      exact le_of_mul_le_mul_right this hsp
    calc s ≤ θ * l2Norm u := hsle
      _ ≤ θ * (l2Norm c / (1 - δ)) := mul_le_mul_of_nonneg_left hule' hθ0
      _ = R := by rw [hR]; ring
  -- the exceptional set
  have hsq : 0 < Real.sqrt (S' : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS')
  set E := Finset.univ.filter (fun j => j ∉ T ∧ R / Real.sqrt S' < |a j|) with hEdef
  have hEdis : Disjoint E T := by
    rw [Finset.disjoint_left]; intro j hj; rw [hEdef, Finset.mem_filter] at hj; exact hj.2.1
  have hEcard : E.card ≤ S' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨E', hE'E, hE'c⟩ := Finset.exists_subset_card_eq hcon.le
    have hb := hL2 E' (Finset.disjoint_of_subset_left hE'E hEdis) hE'c.le
    rw [Real.sqrt_le_left hR0] at hb
    have hne : E'.Nonempty := Finset.card_pos.mp (by omega)
    have hlt : ∑ j ∈ E', (R / Real.sqrt S') ^ 2 < ∑ j ∈ E', a j ^ 2 := by
      apply Finset.sum_lt_sum_of_nonempty hne
      intro j hj
      have hjE := hE'E hj
      rw [hEdef, Finset.mem_filter] at hjE
      rw [← sq_abs (a j)]
      exact pow_lt_pow_left₀ hjE.2.2 (by positivity) (by norm_num)
    rw [Finset.sum_const, hE'c, nsmul_eq_mul, div_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ S')] at hlt
    have hS'pos : (0 : ℝ) < S' := by exact_mod_cast hS'
    rw [mul_div_cancel₀ _ hS'pos.ne'] at hlt
    linarith
  refine ⟨w, ?_, hwT, ⟨E, hEdis, hEcard, ?_, hL2 E hEdis hEcard⟩, ?_⟩
  · -- `w = ∑ uⱼ vⱼ` lies in the column span
    have : w = ∑ j, u j • column F j := by
      funext i
      simp only [hwdef, Matrix.mulVec, dotProduct, column, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro j hjT hjE
    have hn : ¬ (R / Real.sqrt S' < |a j|) := by
      intro hlt; apply hjE; rw [hEdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hjT, hlt⟩
    push Not at hn
    have heq : θ / ((1 - δ) * Real.sqrt S') * l2Norm c = R / Real.sqrt S' := by
      rw [hR]; field_simp
    rw [heq]; exact hn
  · -- size of `w`
    have hb := (iso_bounds F S T hT u hus).2
    rw [← hδdef, ← hwdef] at hb
    have hw1 : l2Norm w ≤ Real.sqrt (1 + δ) * l2Norm u := by
      rw [← Real.sqrt_sq (l2_nonneg w), ← Real.sqrt_sq (l2_nonneg u),
        ← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt hb
    have habs1 : |δ| = δ := abs_of_nonneg hδ0
    have habs2 : |1 - δ| = 1 - δ := abs_of_pos hpos
    simp only [habs1, habs2]
    calc l2Norm w ≤ Real.sqrt (1 + δ) * l2Norm u := hw1
      _ ≤ Real.sqrt (1 + δ) * (l2Norm c / (1 - δ)) :=
          mul_le_mul_of_nonneg_left hule' (Real.sqrt_nonneg _)
      _ = Real.sqrt (1 + δ) / (1 - δ) * l2Norm c := by ring
      _ ≤ (Real.sqrt (1 + δ) / (1 - δ) + 1) * l2Norm c := by
          nlinarith [l2_nonneg c]
