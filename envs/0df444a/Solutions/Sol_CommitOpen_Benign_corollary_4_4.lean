-- Prove2me | solution 1 for CommitOpen.Benign.corollary_4_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:29:17.990346+00:00
-- url     : https://prove2.me/submissions/346a225b-783d-42d8-bc03-8d6b07a063d9

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign
open scoped ComplexOrder InnerProductSpace
open Matrix


/-- single qubit overlap -/
noncomputable def ov (θ θ' b c : Bool) : ℂ := ∑ z : Bool, star (ketBit θ b z) * ketBit θ' c z

lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℂ) := by
  have h : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  have h0 : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
    intro h'; rw [h'] at h; simp at h
  field_simp
  rw [← h]; ring

lemma ov_same (θ b c : Bool) : ov θ θ b c = if b = c then 1 else 0 := by
  have := sqrt2_inv_sq
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1/2 := by rw [sq]; exact this
  cases θ <;> cases b <;> cases c <;>
    simp [ov, ketBit, this] <;> norm_num

lemma ov_sq (θ θ' b c : Bool) : ‖ov θ θ' b c‖ ^ 2 ≤ if θ = θ' then 1 else 1 / 2 := by
  have hn : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = 1/2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by norm_num)]; norm_num
  have := sqrt2_inv_sq
  cases θ <;> cases θ' <;> cases b <;> cases c <;>
    simp [ov, ketBit, hn, this] <;> norm_num [hn]

lemma ov_orth (θ θ' c c' : Bool) : ∑ b : Bool, star (ov θ θ' b c) * ov θ θ' b c' = if c = c' then 1 else 0 := by
  have := sqrt2_inv_sq
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1/2 := by rw [sq]; exact this
  cases θ <;> cases θ' <;> cases c <;> cases c' <;>
    simp [ov, ketBit, this] <;> norm_num


lemma prod_ov {m : ℕ} (θ θ' y z : Fin m → Bool) :
    ∑ a : Fin m → Bool, star (bb84Ket θ y a) * bb84Ket θ' z a = ∏ i, ov (θ i) (θ' i) (y i) (z i) := by
  have : ∀ a : Fin m → Bool, star (bb84Ket θ y a) * bb84Ket θ' z a
      = ∏ i, (star (ketBit (θ i) (y i) (a i)) * ketBit (θ' i) (z i) (a i)) := by
    intro a
    simp [bb84Ket, star_prod, Finset.prod_mul_distrib]
  simp_rw [this]
  unfold ov
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool))
    (fun i b => star (ketBit (θ i) (y i) b) * ketBit (θ' i) (z i) b), Fintype.piFinset_univ]

lemma ket_orth {m : ℕ} (θ y z : Fin m → Bool) :
    ∑ a : Fin m → Bool, star (bb84Ket θ y a) * bb84Ket θ z a = if y = z then 1 else 0 := by
  rw [prod_ov]
  simp_rw [ov_same]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma ket_complete {m : ℕ} (θ : Fin m → Bool) (a a' : Fin m → Bool) :
    ∑ z : Fin m → Bool, bb84Ket θ z a * star (bb84Ket θ z a') = if a = a' then 1 else 0 := by
  classical
  set U : Matrix (Fin m → Bool) (Fin m → Bool) ℂ := Matrix.of fun z a => star (bb84Ket θ z a) with hU
  have h1 : U * Uᴴ = 1 := by
    ext z z'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU, Matrix.of_apply, star_star,
      Matrix.one_apply]
    rw [ket_orth]
  have h2 : Uᴴ * U = 1 := by
    exact mul_eq_one_comm.mp h1
  have := congrFun (congrFun h2 a) a'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU, Matrix.of_apply, star_star,
      Matrix.one_apply] at this
  rw [← this]



lemma ball_count {α : Type} [DecidableEq α] (U : Finset α) (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1/2) :
    (((U.powerset).filter (fun S => (S.card : ℝ) ≤ μ * U.card)).card : ℝ)
      ≤ (2:ℝ) ^ (binEntropy2 μ * U.card) := by
  set n := U.card with hn
  set B := (U.powerset).filter (fun S => (S.card : ℝ) ≤ μ * n) with hB
  have hμ1 : μ < 1 := by linarith
  have h1μ : 0 < 1 - μ := by linarith
  have hsum : ∑ S ∈ U.powerset, μ ^ S.card * (1 - μ) ^ (n - S.card) = 1 := by
    rw [Finset.sum_pow_mul_eq_add_pow]; simp
  have hlow : ∀ S ∈ B, Real.exp (-(n * Real.binEntropy μ)) ≤ μ ^ S.card * (1 - μ) ^ (n - S.card) := by
    intro S hS
    rw [hB, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSU, hSc⟩ := hS
    have hle : S.card ≤ n := Finset.card_le_card hSU
    have hpos : 0 < μ ^ S.card * (1 - μ) ^ (n - S.card) := by positivity
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    have hcast : ((n - S.card : ℕ) : ℝ) = (n : ℝ) - S.card := by rw [Nat.cast_sub hle]
    rw [hcast]
    have hlog : Real.log μ ≤ Real.log (1 - μ) := Real.log_le_log h0 (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hSc) (sub_nonneg.mpr hlog)]
  have hcount : (B.card : ℝ) * Real.exp (-(n * Real.binEntropy μ)) ≤ 1 := by
    calc (B.card : ℝ) * Real.exp (-(n * Real.binEntropy μ))
        = ∑ S ∈ B, Real.exp (-(n * Real.binEntropy μ)) := by simp
      _ ≤ ∑ S ∈ B, μ ^ S.card * (1 - μ) ^ (n - S.card) := Finset.sum_le_sum hlow
      _ ≤ ∑ S ∈ U.powerset, μ ^ S.card * (1 - μ) ^ (n - S.card) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro S _ _
          positivity
      _ = 1 := hsum
  have hexp : (2:ℝ) ^ (binEntropy2 μ * n) = Real.exp (n * Real.binEntropy μ) := by
    rw [Real.rpow_def_of_pos (by norm_num), binEntropy2]
    congr 1
    have : Real.log 2 ≠ 0 := by positivity
    field_simp
  rw [hexp]
  have hpe : 0 < Real.exp (n * Real.binEntropy μ) := Real.exp_pos _
  have : Real.exp (-(n * Real.binEntropy μ)) = (Real.exp (n * Real.binEntropy μ))⁻¹ := by
    rw [Real.exp_neg]
  rw [this] at hcount
  rw [← div_eq_mul_inv, div_le_one hpe] at hcount
  exact hcount

lemma J_card {m k : ℕ} (ε : ℝ) (hε : 0 < ε) (xhat x : Fin m → Bool) (t : Test m k)
    (herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2) :
    (((goodSet ε xhat t ∩ agreeOn t.1.1 x).card : ℕ) : ℝ) ≤
      (2:ℝ) ^ (binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ)) := by
  classical
  set T := t.1.1 with hT
  set T' := t.1.2 with hT'
  have hsub : T' ⊆ T := t.2.2
  set r := relHamming T' x xhat with hr
  have hr0 : 0 ≤ r := by
    rw [hr]; unfold relHamming; positivity
  have hμ0 : 0 < r + ε := by linarith
  set D : (Fin m → Bool) → Finset (Fin m) := fun z => Tᶜ.filter (fun i => z i ≠ xhat i) with hD
  have hinj : Set.InjOn D ↑(goodSet ε xhat t ∩ agreeOn T x) := by
    intro z hz z' hz' hzz
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, agreeOn, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz hz'
    funext i
    by_cases hi : i ∈ T
    · rw [hz.2 i hi, hz'.2 i hi]
    · have : i ∈ D z ↔ i ∈ D z' := by rw [hzz]
      simp only [hD, Finset.mem_filter, Finset.mem_compl, hi, not_false_eq_true, true_and] at this
      by_contra hne
      cases h1 : z i <;> cases h2 : z' i <;> cases h3 : xhat i <;> simp_all
  have hmaps : ∀ z ∈ goodSet ε xhat t ∩ agreeOn T x,
      D z ∈ (Tᶜ.powerset).filter (fun S => (S.card : ℝ) ≤ (r + ε) * (Tᶜ.card : ℝ)) := by
    intro z hz
    rw [Finset.mem_inter, goodSet, Finset.mem_filter, agreeOn, Finset.mem_filter] at hz
    obtain ⟨⟨_, hg⟩, _, hagree⟩ := hz
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    have hr' : relHamming T' z xhat = r := by
      unfold relHamming hammingOn
      have : T'.filter (fun i => z i ≠ xhat i) = T'.filter (fun i => x i ≠ xhat i) := by
        apply Finset.filter_congr
        intro i hi
        rw [hagree i (hsub hi)]
      rw [this]; rfl
    rw [hr'] at hg
    by_cases hn : Tᶜ.card = 0
    · have : D z = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i hi
        have : i ∈ Tᶜ := (Finset.mem_filter.mp hi).1
        rw [Finset.card_eq_zero] at hn
        simp [hn] at this
      rw [this, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hμ0.le (Nat.cast_nonneg _)
    · have hnpos : (0:ℝ) < Tᶜ.card := by exact_mod_cast Nat.pos_of_ne_zero hn
      unfold relHamming hammingOn at hg
      rw [div_le_iff₀ hnpos] at hg
      exact hg
  have hcard := Finset.card_le_card_of_injOn D hmaps hinj
  calc ((goodSet ε xhat t ∩ agreeOn T x).card : ℝ)
      ≤ (((Tᶜ.powerset).filter (fun S => (S.card : ℝ) ≤ (r + ε) * (Tᶜ.card : ℝ))).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ _ := ball_count Tᶜ (r + ε) hμ0 herr



lemma inner_self_C {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] (v : F) :
    ⟪v, v⟫_ℂ = ((‖v‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K v

lemma L1_sum {ι κ F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (Y : Finset ι) (W : Finset κ) [DecidableEq κ] (f : κ → F) (μ : ι → κ → ℂ)
    (horth : ∀ w ∈ W, ∀ w' ∈ W, ∑ y ∈ Y, star (μ y w) * μ y w' = if w = w' then 1 else 0) :
    ∑ y ∈ Y, ‖∑ w ∈ W, μ y w • f w‖ ^ 2 = ∑ w ∈ W, ‖f w‖ ^ 2 := by
  have h1 : ∀ y, ((‖∑ w ∈ W, μ y w • f w‖ : ℂ)) ^ 2 =
      ∑ w ∈ W, ∑ w' ∈ W, star (μ y w) * μ y w' * ⟪f w, f w'⟫_ℂ := by
    intro y
    rw [← inner_self_C, sum_inner]
    apply Finset.sum_congr rfl
    intro w _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro w' _
    rw [inner_smul_left, inner_smul_right]
    simp [mul_assoc]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ w ∈ W, ∑ y ∈ Y, ∑ w' ∈ W, star (μ y w) * μ y w' * ⟪f w, f w'⟫_ℂ
      = (‖f w‖ : ℂ) ^ 2 := by
    intro w hw
    rw [Finset.sum_comm]
    have : ∀ w' ∈ W, ∑ y ∈ Y, star (μ y w) * μ y w' * ⟪f w, f w'⟫_ℂ
        = (if w = w' then ⟪f w, f w'⟫_ℂ else 0) := by
      intro w' hw'
      rw [← Finset.sum_mul, horth w hw w' hw']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this]
    simp [hw, inner_self_C]
  exact Finset.sum_congr rfl h2


lemma L1_bound {ι κ F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (W : Finset κ) (f : κ → F) (μ : ι → κ → ℂ) (c : ℝ) (y : ι)
    (hb : ∀ w ∈ W, ‖μ y w‖ ^ 2 ≤ c) :
    ‖∑ w ∈ W, μ y w • f w‖ ^ 2 ≤ W.card * c * ∑ w ∈ W, ‖f w‖ ^ 2 := by
  have h1 : ‖∑ w ∈ W, μ y w • f w‖ ≤ ∑ w ∈ W, ‖μ y w‖ * ‖f w‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro w _
    rw [norm_smul]
  have h2 : (∑ w ∈ W, ‖μ y w‖ * ‖f w‖) ^ 2 ≤ W.card * ∑ w ∈ W, (‖μ y w‖ * ‖f w‖) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ w ∈ W, (‖μ y w‖ * ‖f w‖) ^ 2 ≤ c * ∑ w ∈ W, ‖f w‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hb w hw) (sq_nonneg _)
  calc ‖∑ w ∈ W, μ y w • f w‖ ^ 2 ≤ (∑ w ∈ W, ‖μ y w‖ * ‖f w‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ W.card * ∑ w ∈ W, (‖μ y w‖ * ‖f w‖) ^ 2 := h2
    _ ≤ W.card * (c * ∑ w ∈ W, ‖f w‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ = _ := by ring

noncomputable def muI {m : ℕ} (θ θhat : Fin m → Bool) (I : Finset (Fin m)) (y w : Fin m → Bool) : ℂ :=
  ∏ i ∈ I, ov (θ i) (θhat i) (y i) (w i)

lemma agreeOn_eq_piFinset {m : ℕ} (I : Finset (Fin m)) (x : Fin m → Bool) :
    agreeOn Iᶜ x = Fintype.piFinset (fun i => if i ∈ I then (Finset.univ : Finset Bool) else {x i}) := by
  ext y
  simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    Finset.mem_compl]
  constructor
  · intro h i
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi, h i hi]
  · intro h i hi
    have := h i
    simpa [hi] using this

lemma muI_orth {m : ℕ} (θ θhat : Fin m → Bool) (I : Finset (Fin m)) (x w w' : Fin m → Bool)
    (hw : ∀ i, i ∉ I → w i = false) (hw' : ∀ i, i ∉ I → w' i = false) :
    ∑ y ∈ agreeOn Iᶜ x, star (muI θ θhat I y w) * muI θ θhat I y w' = if w = w' then 1 else 0 := by
  classical
  have h1 : ∀ y : Fin m → Bool, star (muI θ θhat I y w) * muI θ θhat I y w' =
      ∏ i, (if i ∈ I then star (ov (θ i) (θhat i) (y i) (w i)) * ov (θ i) (θhat i) (y i) (w' i) else 1) := by
    intro y
    unfold muI
    rw [star_prod, ← Finset.prod_mul_distrib]
    rw [Finset.prod_ite_mem Finset.univ I]
    simp
  simp_rw [h1]
  rw [agreeOn_eq_piFinset, ← Finset.prod_univ_sum (fun i => if i ∈ I then (Finset.univ : Finset Bool) else {x i})
    (fun i b => if i ∈ I then star (ov (θ i) (θhat i) b (w i)) * ov (θ i) (θhat i) b (w' i) else 1)]
  have h2 : ∀ i, ∑ b ∈ (if i ∈ I then (Finset.univ : Finset Bool) else {x i}),
      (if i ∈ I then star (ov (θ i) (θhat i) b (w i)) * ov (θ i) (θhat i) b (w' i) else 1)
      = if w i = w' i then 1 else 0 := by
    intro i
    by_cases hi : i ∈ I
    · simp only [hi, if_true]
      exact ov_orth _ _ _ _
    · simp [hi, hw i hi, hw' i hi]
  simp_rw [h2]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma muI_sq {m : ℕ} (θ θhat : Fin m → Bool) (I : Finset (Fin m)) (y w : Fin m → Bool) :
    ‖muI θ θhat I y w‖ ^ 2 ≤ (1/2 : ℝ) ^ (hammingOn I θ θhat) := by
  unfold muI hammingOn
  rw [norm_prod, ← Finset.prod_pow]
  calc ∏ i ∈ I, ‖ov (θ i) (θhat i) (y i) (w i)‖ ^ 2
      ≤ ∏ i ∈ I, (if θ i = θhat i then (1:ℝ) else 1/2) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; exact ov_sq _ _ _ _
    _ = _ := by
        rw [Finset.prod_ite]
        simp [Finset.filter_not]


lemma psi_expand {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool)
    (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (a : Fin m → Bool) (e : E) :
    ψ (a, e) = ∑ z : Fin m → Bool, bb84Ket θ z a * amp θ z ψ e := by
  unfold amp ampAlong
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ a' : Fin m → Bool, ∑ z : Fin m → Bool, bb84Ket θ z a * (star (bb84Ket θ z a') * ψ (a', e))
      = (if a = a' then 1 else 0) * ψ (a', e) := by
    intro a'
    rw [← ket_complete θ a a', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    ring
  simp_rw [this]
  simp

lemma amp_expand {m : ℕ} {E : Type} [Fintype E] (θs θh : Fin m → Bool)
    (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (y : Fin m → Bool) (e : E) :
    amp θs y ψ e = ∑ z : Fin m → Bool, (∏ i, ov (θs i) (θh i) (y i) (z i)) * amp θh z ψ e := by
  conv_lhs => unfold amp ampAlong
  simp_rw [psi_expand θh ψ _ e, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← prod_ov, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

noncomputable def piI {m : ℕ} (I : Finset (Fin m)) (z : Fin m → Bool) : Fin m → Bool :=
  fun i => if i ∈ I then z i else false

noncomputable def gam {m : ℕ} (θs θh : Fin m → Bool) (I : Finset (Fin m)) (x z : Fin m → Bool) : ℂ :=
  ∏ i ∈ Iᶜ, ov (θs i) (θh i) (x i) (z i)

lemma M_split {m : ℕ} (T I : Finset (Fin m)) (hI : I ⊆ Tᶜ) (θh θ x y z : Fin m → Bool)
    (hy : y ∈ agreeOn Iᶜ x) :
    ∏ i, ov (mixBasis T θh θ i) (θh i) (y i) (z i)
      = muI θ θh I y (piI I z) * gam (mixBasis T θh θ) θh I x z := by
  rw [← Finset.prod_mul_prod_compl I]
  congr 1
  · unfold muI
    apply Finset.prod_congr rfl
    intro i hi
    have hiT : i ∉ T := by simpa using hI hi
    simp [mixBasis, hiT, piI, hi]
  · unfold gam
    apply Finset.prod_congr rfl
    intro i hi
    have : y i = x i := by
      simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hy i hi
    rw [this]

lemma minent_core {m : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (θh θ x : Fin m → Bool) (T I : Finset (Fin m)) (hI : I ⊆ Tᶜ)
    (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (J : Finset (Fin m → Bool))
    (hJ : ∀ z, amp θh z ψ ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J) :
    ∀ y0 ∈ agreeOn Iᶜ x, outcomeProb (mixBasis T θh θ) ψ y0 ≤
      J.card * (1/2 : ℝ) ^ (hammingOn I θ θh) *
        ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis T θh θ) ψ y := by
  classical
  set θs := mixBasis T θh θ with hθs
  let ev : (Fin m → Bool) → EuclideanSpace ℂ E := fun z => WithLp.toLp 2 (amp θh z ψ)
  have hStepA : ∀ y ∈ agreeOn Iᶜ x,
      (WithLp.toLp 2 (amp θs y ψ) : EuclideanSpace ℂ E) =
        ∑ z ∈ J, (∏ i, ov (θs i) (θh i) (y i) (z i)) • ev z := by
    intro y hy
    ext e'
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
    show amp θs y ψ e' = ∑ z ∈ J, (∏ i, ov (θs i) (θh i) (y i) (z i)) * amp θh z ψ e'
    rw [amp_expand θs θh ψ y e']
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hzJ
    by_cases h0 : amp θh z ψ e' = 0
    · rw [h0, mul_zero]
    · by_contra hne
      have hz1 : amp θh z ψ ≠ 0 := fun h => h0 (by rw [h]; rfl)
      have hnot : ¬ (∀ i ∈ T, z i = x i) := fun h => hzJ (hJ z hz1 h)
      simp only [not_forall] at hnot
      obtain ⟨i, hiT, hzi⟩ := hnot
      have hiI : i ∈ Iᶜ :=
        Finset.mem_compl.mpr (fun hiI => (Finset.mem_compl.mp (hI hiI)) hiT)
      have hyi : y i = x i := by
        simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy i hiI
      have : ∏ i, ov (θs i) (θh i) (y i) (z i) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        have hθ : θs i = θh i := by simp [hθs, mixBasis, hiT]
        rw [hθ, ov_same, if_neg]
        rw [hyi]; exact fun h => hzi h.symm
      exact hne (by rw [this, zero_mul])
  have hStepB : ∀ y, outcomeProb θs ψ y = ‖(WithLp.toLp 2 (amp θs y ψ) : EuclideanSpace ℂ E)‖ ^ 2 := by
    intro y
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  -- grouping
  set W : Finset (Fin m → Bool) := J.image (piI I) with hW
  let f : (Fin m → Bool) → EuclideanSpace ℂ E := fun w =>
    ∑ z ∈ J.filter (fun z => piI I z = w), gam θs θh I x z • ev z
  have hStepC : ∀ y ∈ agreeOn Iᶜ x,
      (WithLp.toLp 2 (amp θs y ψ) : EuclideanSpace ℂ E) = ∑ w ∈ W, muI θ θh I y w • f w := by
    intro y hy
    rw [hStepA y hy]
    have h1 : ∀ z ∈ J, (∏ i, ov (θs i) (θh i) (y i) (z i)) • ev z
        = muI θ θh I y (piI I z) • (gam θs θh I x z • ev z) := by
      intro z _
      rw [M_split T I hI θh θ x y z hy, mul_smul]
    rw [Finset.sum_congr rfl h1]
    rw [← Finset.sum_fiberwise_of_maps_to (s := J) (t := W) (g := piI I)
      (fun z hz => Finset.mem_image_of_mem _ hz)]
    apply Finset.sum_congr rfl
    intro w _
    simp only [f]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  have hzero : ∀ w ∈ W, ∀ i, i ∉ I → w i = false := by
    intro w hw i hi
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    simp [piI, hi]
  have horth : ∀ w ∈ W, ∀ w' ∈ W,
      ∑ y ∈ agreeOn Iᶜ x, star (muI θ θh I y w) * muI θ θh I y w' = if w = w' then 1 else 0 :=
    fun w hw w' hw' => muI_orth θ θh I x w w' (hzero w hw) (hzero w' hw')
  have hS := L1_sum (agreeOn Iᶜ x) W f (muI θ θh I) horth
  intro y0 hy0
  rw [hStepB y0, hStepC y0 hy0]
  have hsum : ∑ y ∈ agreeOn Iᶜ x, outcomeProb θs ψ y = ∑ w ∈ W, ‖f w‖ ^ 2 := by
    rw [← hS]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hStepB y, hStepC y hy]
  rw [hsum]
  have hb := L1_bound W f (muI θ θh I) ((1/2 : ℝ) ^ (hammingOn I θ θh)) y0
    (fun w _ => muI_sq θ θh I y0 w)
  refine hb.trans ?_
  have hWc : (W.card : ℝ) ≤ J.card := by
    exact_mod_cast Finset.card_image_le
  have hnn : 0 ≤ ∑ w ∈ W, ‖f w‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : (0:ℝ) ≤ (1/2 : ℝ) ^ (hammingOn I θ θh) := by positivity
  calc (W.card : ℝ) * (1 / 2 : ℝ) ^ hammingOn I θ θh * ∑ w ∈ W, ‖f w‖ ^ 2
      ≤ (J.card : ℝ) * (1 / 2 : ℝ) ^ hammingOn I θ θh * ∑ w ∈ W, ‖f w‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hnn
        exact mul_le_mul_of_nonneg_right hWc hc
    _ = _ := by rfl

lemma amp_restrict {m : ℕ} {E : Type} [Fintype E] (T : Finset (Fin m))
    (θh θ x : Fin m → Bool) (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (J : Finset (Fin m → Bool))
    (hJ : ∀ z, amp θh z ψ ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J)
    (y : Fin m → Bool) (hy : ∀ i ∈ T, y i = x i) (e' : E) :
    amp (mixBasis T θh θ) y ψ e' =
      ∑ z ∈ J, (∏ i, ov (mixBasis T θh θ i) (θh i) (y i) (z i)) * amp θh z ψ e' := by
  rw [amp_expand (mixBasis T θh θ) θh ψ y e']
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro z _ hzJ
  by_cases h0 : amp θh z ψ e' = 0
  · rw [h0, mul_zero]
  · by_contra hne
    have hz1 : amp θh z ψ ≠ 0 := fun h => h0 (by rw [h]; rfl)
    have hnot : ¬ (∀ i ∈ T, z i = x i) := fun h => hzJ (hJ z hz1 h)
    simp only [not_forall] at hnot
    obtain ⟨i, hiT, hzi⟩ := hnot
    have hyi : y i = x i := hy i hiT
    have : ∏ i, ov (mixBasis T θh θ i) (θh i) (y i) (z i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hθ : mixBasis T θh θ i = θh i := by simp [mixBasis, hiT]
      rw [hθ, ov_same, if_neg]
      rw [hyi]; exact fun h => hzi h.symm
    exact hne (by rw [this, zero_mul])

lemma bob_rank {m : ℕ} {E : Type} [Fintype E] [DecidableEq E] (T : Finset (Fin m))
    (θh θ x : Fin m → Bool) (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (J : Finset (Fin m → Bool))
    (hJ : ∀ z, amp θh z ψ ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J) :
    (bobState (mixBasis T θh θ) ψ T x).rank ≤ J.card := by
  classical
  set A : Matrix E (agreeOn T x) ℂ := Matrix.of fun e y => amp (mixBasis T θh θ) y.1 ψ e with hA
  set B : Matrix E J ℂ := Matrix.of fun e z => amp θh z.1 ψ e with hB
  set C : Matrix J (agreeOn T x) ℂ :=
    Matrix.of fun z y => ∏ i, ov (mixBasis T θh θ i) (θh i) (y.1 i) (z.1 i) with hC
  have h1 : bobState (mixBasis T θh θ) ψ T x = A * Aᴴ := by
    ext e e'
    simp only [bobState, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hA, Matrix.of_apply, Pi.star_apply]
    exact (Finset.sum_coe_sort (agreeOn T x) (fun y => amp (mixBasis T θh θ) y ψ e *
      star (amp (mixBasis T θh θ) y ψ e'))).symm
  have h2 : A = B * C := by
    ext e y
    simp only [hA, hB, hC, Matrix.of_apply, Matrix.mul_apply]
    have hy : ∀ i ∈ T, y.1 i = x i := by
      have := y.2
      simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [amp_restrict T θh θ x ψ J hJ y.1 hy e]
    rw [← Finset.sum_coe_sort J]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [h1]
  calc (A * Aᴴ).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ = (B * C).rank := by rw [h2]
    _ ≤ B.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card J := Matrix.rank_le_card_width _
    _ = J.card := Fintype.card_coe J

lemma binEntropy2_nonneg {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) : 0 ≤ binEntropy2 μ := by
  unfold binEntropy2
  exact div_nonneg (Real.binEntropy_nonneg h0 h1) (Real.log_nonneg (by norm_num))

theorem cor44_aux {m k : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ε : ℝ) (hε : 0 < ε)
    (xhat θhat θ : Fin m → Bool) (t : Test m k)
    (φt : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hunit : ‖φt‖ = 1)
    (hform : ∀ y, y ∉ goodSet ε xhat t → amp θhat y φt = 0)
    (x : Fin m → Bool) (herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2)
    (hpos : 0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) φt y) :
    maxEntropy (bobState (mixBasis t.1.1 θhat θ) φt t.1.1 x) ≤
        binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ∧
      ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
        0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) φt y →
        (hammingOn I θ θhat : ℝ) - binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ≤
          condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) φt) I x := by
  classical
  set T := t.1.1 with hT
  set H := binEntropy2 (relHamming t.1.2 x xhat + ε) with hH
  set J := goodSet ε xhat t ∩ agreeOn T x with hJdef
  have hr0 : 0 ≤ relHamming t.1.2 x xhat := by unfold relHamming; positivity
  have hH0 : 0 ≤ H := binEntropy2_nonneg (by linarith) (by linarith)
  have hJ : ∀ z, amp θhat z φt ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J := by
    intro z hz hz2
    rw [hJdef, Finset.mem_inter]
    refine ⟨?_, ?_⟩
    · by_contra hn
      exact hz (hform z hn)
    · simpa [agreeOn] using hz2
  have hJcard := J_card ε hε xhat x t herr
  have hn0 : (0:ℝ) ≤ (Tᶜ.card : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have hrk := bob_rank T θhat θ x φt J hJ
    unfold maxEntropy
    by_cases hr : (bobState (mixBasis T θhat θ) φt T x).rank = 0
    · rw [hr]; simp; exact mul_nonneg hH0 hn0
    · have hrpos : (0:ℝ) < ((bobState (mixBasis T θhat θ) φt T x).rank : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hr
      calc Real.logb 2 ((bobState (mixBasis T θhat θ) φt T x).rank : ℝ)
          ≤ Real.logb 2 ((2:ℝ) ^ (H * (Tᶜ.card : ℝ))) := by
            apply Real.logb_le_logb_of_le (by norm_num) hrpos
            exact le_trans (by exact_mod_cast hrk) hJcard
        _ = H * (Tᶜ.card : ℝ) := Real.logb_rpow (by norm_num) (by norm_num)
  · intro I hI hposI
    set P := outcomeProb (mixBasis T θhat θ) φt with hP
    set S := ∑ y ∈ agreeOn Iᶜ x, P y with hS
    have hcore := minent_core θhat θ x T I hI φt J hJ
    have hbound : ∀ y ∈ agreeOn Iᶜ x, P y / S ≤ (2:ℝ) ^ (H * (Tᶜ.card : ℝ) - (hammingOn I θ θhat : ℝ)) := by
      intro y hy
      rw [div_le_iff₀ hposI]
      have h1 := hcore y hy
      have h2 : (J.card : ℝ) * (1/2 : ℝ) ^ (hammingOn I θ θhat) ≤
          (2:ℝ) ^ (H * (Tᶜ.card : ℝ) - (hammingOn I θ θhat : ℝ)) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, one_div, inv_pow, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right hJcard (by positivity)
      calc P y ≤ (J.card : ℝ) * (1/2 : ℝ) ^ (hammingOn I θ θhat) * S := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 hposI.le
    obtain ⟨y1, hy1, hy1pos⟩ : ∃ y ∈ agreeOn Iᶜ x, 0 < P y := by
      by_contra hcon
      simp only [not_exists, not_and, not_lt] at hcon
      have : S ≤ 0 := Finset.sum_nonpos hcon
      linarith
    unfold condMinEntropy
    have hsup_pos : 0 < (agreeOn Iᶜ x).sup' ⟨x, self_mem_agreeOn Iᶜ x⟩ (fun y => P y / S) := by
      refine lt_of_lt_of_le ?_ (Finset.le_sup' (fun y => P y / S) hy1)
      exact div_pos hy1pos hposI
    have hsup_le : (agreeOn Iᶜ x).sup' ⟨x, self_mem_agreeOn Iᶜ x⟩ (fun y => P y / S)
        ≤ (2:ℝ) ^ (H * (Tᶜ.card : ℝ) - (hammingOn I θ θhat : ℝ)) :=
      Finset.sup'_le _ _ hbound
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hsup_pos hsup_le
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
    linarith

end CommitOpen.Benign

open CommitOpen.Benign

theorem solution {m k : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ε : ℝ) (hε : 0 < ε)
    (xhat θhat θ : Fin m → Bool) (t : Test m k)
    (φt : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hunit : ‖φt‖ = 1)
    (hform : ∀ y, y ∉ goodSet ε xhat t → amp θhat y φt = 0)
    (x : Fin m → Bool) (herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2)
    (hpos : 0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) φt y) :
    maxEntropy (bobState (mixBasis t.1.1 θhat θ) φt t.1.1 x) ≤
        binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ∧
      ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
        0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) φt y →
        (hammingOn I θ θhat : ℝ) - binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ≤
          condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) φt) I x :=
  cor44_aux ε hε xhat θhat θ t φt hunit hform x herr hpos
