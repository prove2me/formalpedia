-- Prove2me | solution 1 for BertsekasDP.average_cost_policy_iteration
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-08T04:11:23.198953+00:00
-- url     : https://prove2.me/submissions/0d23095b-34ab-4dfd-a0cd-cbce264f9b8d

import Mathlib
import Definitions.Def_BertsekasSSPModel

open Finset

namespace AC

variable {n : ℕ} {C : Type} [Fintype C]

/-- One-step transition operator of a stationary policy `μ`. -/
def Pop (M : BertsekasSSPModel n C) (μ : Fin n → C) (e : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, M.p i (μ i) j * e j

/-- The transition operator with the reference state `s` killed. -/
def Qop (M : BertsekasSSPModel n C) (s : Fin n) (μ : Fin n → C) (e : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, if j = s then 0 else M.p i (μ i) j * e j

variable (M : BertsekasSSPModel n C) (s : Fin n) (μ : Fin n → C)

lemma Qop_eq_Pop {e : Fin n → ℝ} (he : e s = 0) : Qop M s μ e = Pop M μ e := by
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = s
  · subst hj; simp [he]
  · simp [hj]

lemma Qop_add (e f : Fin n → ℝ) :
    Qop M s μ (e + f) = Qop M s μ e + Qop M s μ f := by
  funext i
  simp only [Qop, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = s <;> simp [hj, mul_add]

lemma Qop_smul (c : ℝ) (e : Fin n → ℝ) :
    Qop M s μ (c • e) = c • Qop M s μ e := by
  funext i
  simp only [Qop, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = s <;> simp [hj] <;> ring

lemma Qop_mono {e f : Fin n → ℝ} (h : ∀ i, e i ≤ f i) (i : Fin n) :
    Qop M s μ e i ≤ Qop M s μ f i := by
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j = s
  · simp [hj]
  · simp only [hj, if_false]
    exact mul_le_mul_of_nonneg_left (h j) (M.hp_nonneg _ _ _)

lemma Qop_nonneg {e : Fin n → ℝ} (h : ∀ i, 0 ≤ e i) (i : Fin n) :
    0 ≤ Qop M s μ e i := by
  have := Qop_mono M s μ (e := 0) (f := e) (by simpa using h) i
  simpa [Qop] using this

lemma Qop_one_le (hμ : ∀ i, μ i ∈ M.U i) (i : Fin n) :
    Qop M s μ 1 i ≤ 1 := by
  have h1 : Qop M s μ 1 i ≤ ∑ j, M.p i (μ i) j := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = s
    · simpa [hj] using M.hp_nonneg i (μ i) j
    · simp [hj]
  exact h1.trans (M.hp_sum i (μ i) (hμ i))

/-- `Qop` applied to a constant vector, evaluated pointwise. -/
lemma Qop_const (c : ℝ) (i : Fin n) :
    Qop M s μ (fun _ => c) i = c * Qop M s μ 1 i := by
  have : (fun _ : Fin n => c) = c • (1 : Fin n → ℝ) := by
    funext j; simp
  rw [this, Qop_smul]
  simp

lemma Qit_mono (m : ℕ) {e f : Fin n → ℝ} (h : ∀ i, e i ≤ f i) (i : Fin n) :
    (Qop M s μ)^[m] e i ≤ (Qop M s μ)^[m] f i := by
  induction m generalizing i with
  | zero => simpa using h i
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Qop_mono M s μ (fun j => ih j) i

lemma Qit_smul (m : ℕ) (c : ℝ) (e : Fin n → ℝ) :
    (Qop M s μ)^[m] (c • e) = c • (Qop M s μ)^[m] e := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Qop_smul]

lemma Qit_neg (m : ℕ) (e : Fin n → ℝ) :
    (Qop M s μ)^[m] (-e) = -(Qop M s μ)^[m] e := by
  have h := Qit_smul M s μ m (-1) e
  simpa using h

/-- For a stationary policy, `Q^m 1` is exactly the probability of avoiding `s`
during the first `m` stages. -/
lemma avoid_eq (m : ℕ) :
    BertsekasSSPAvoidProb M s (fun _ => μ) m = (Qop M s μ)^[m] 1 := by
  induction m with
  | zero => funext i; simp [BertsekasSSPAvoidProb]
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      funext i
      show (∑ j, if j = s then 0 else
        M.p i ((fun _ => μ) 0 i) j *
          BertsekasSSPAvoidProb M s (fun k => (fun _ => μ) (k + 1)) m j) = _
      rw [show (fun k => (fun _ : ℕ => μ) (k + 1)) = (fun _ : ℕ => μ) from rfl, ih]
      rfl

end AC

namespace AC

variable {n : ℕ} {C : Type} [Fintype C]
variable (M : BertsekasSSPModel n C) (s : Fin n) (μ : Fin n → C)

lemma Qop_sub (e f : Fin n → ℝ) :
    Qop M s μ (e - f) = Qop M s μ e - Qop M s μ f := by
  have h : e - f = e + (-1 : ℝ) • f := by module
  rw [h, Qop_add, Qop_smul]
  module

lemma Qit_nonneg (m : ℕ) {e : Fin n → ℝ} (h : ∀ i, 0 ≤ e i) (i : Fin n) :
    0 ≤ (Qop M s μ)^[m] e i := by
  induction m generalizing i with
  | zero => simpa using h i
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Qop_nonneg M s μ (fun j => ih j) i

/-- Assumption 7.4.1 gives a uniform contraction factor `ρ < 1` for the policy `μ`. -/
lemma exists_rho (m : ℕ) (hm : ∀ i, (Qop M s μ)^[m] 1 i < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, (Qop M s μ)^[m] 1 i ≤ ρ := by
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ ((Qop M s μ)^[m] 1) ⟨s, Finset.mem_univ s⟩
  exact ⟨_, Qit_nonneg M s μ m (fun _ => zero_le_one) i₀, hm i₀,
    fun i => hi₀ i (Finset.mem_univ i)⟩

lemma Qit_le_of_le (m : ℕ) {ρ : ℝ} (hρle : ∀ i, (Qop M s μ)^[m] 1 i ≤ ρ)
    {e : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ i, e i ≤ c) (i : Fin n) :
    (Qop M s μ)^[m] e i ≤ c * ρ := by
  have h1 : (Qop M s μ)^[m] e i ≤ (Qop M s μ)^[m] (fun _ => c) i :=
    Qit_mono M s μ m he i
  have hcc : (fun _ : Fin n => c) = c • (1 : Fin n → ℝ) := by funext j; simp
  rw [hcc, Qit_smul] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (hρle i) hc)

/-- A vector fixed by the killed operator is zero. -/
lemma eq_zero_of_fixed (m : ℕ) (hm : ∀ i, (Qop M s μ)^[m] 1 i < 1)
    {e : Fin n → ℝ} (hfix : ∀ i, e i = Qop M s μ e i) : ∀ i, e i = 0 := by
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ := exists_rho M s μ m hm
  have hle : ∀ f : Fin n → ℝ, (∀ i, f i = Qop M s μ f i) → ∀ i, f i ≤ 0 := by
    intro f hf i
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ f ⟨s, Finset.mem_univ s⟩
    by_contra hcon
    push_neg at hcon
    have hc : 0 < f i₀ := lt_of_lt_of_le hcon (hi₀ i (Finset.mem_univ i))
    have hfixf : Qop M s μ f = f := funext fun j => (hf j).symm
    have h1 : (Qop M s μ)^[m] f = f := Function.iterate_fixed hfixf m
    have h2 : (Qop M s μ)^[m] f i₀ ≤ f i₀ * ρ :=
      Qit_le_of_le M s μ m hρle hc.le (fun j => hi₀ j (Finset.mem_univ j)) i₀
    rw [h1] at h2
    nlinarith
  intro i
  have h1 := hle e hfix i
  have h2 : ∀ j, (-e) j = Qop M s μ (-e) j := by
    intro j
    have hq : Qop M s μ (-e) = -Qop M s μ e := by
      have := Qop_smul M s μ (-1) e
      simpa using this
    rw [hq]
    simp [← hfix j]
  have h3 := hle (-e) h2 i
  simp only [Pi.neg_apply] at h3
  linarith

/-- The gain never increases: the one-step inequality of policy iteration. -/
lemma beta_nonneg (hμ : ∀ i, μ i ∈ M.U i) {e δ : Fin n → ℝ} {β : ℝ}
    (hes : e s = 0) (hδ : ∀ i, 0 ≤ δ i)
    (heq : ∀ i, e i = Qop M s μ e i + δ i - β) : 0 ≤ β := by
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ e ⟨s, Finset.mem_univ s⟩
  have hd : e i₁ ≤ 0 := le_trans (hi₁ s (Finset.mem_univ s)) (le_of_eq hes)
  have h1 : e i₁ * Qop M s μ 1 i₁ ≤ Qop M s μ e i₁ := by
    have h := Qop_mono M s μ (e := fun _ => e i₁) (f := e)
      (fun j => hi₁ j (Finset.mem_univ j)) i₁
    rwa [Qop_const] at h
  have h2 : e i₁ ≤ e i₁ * Qop M s μ 1 i₁ := by
    nlinarith [Qop_one_le M s μ hμ i₁]
  have h3 := heq i₁
  linarith [hδ i₁]

lemma Qit_le_self (m : ℕ) {e : Fin n → ℝ} (h : ∀ i, Qop M s μ e i ≤ e i) (i : Fin n) :
    (Qop M s μ)^[m] e i ≤ e i := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      exact le_trans (Qit_mono M s μ m h i) (ih i)

/-- If the differential costs satisfy `e = Q e + δ` with `δ ≥ 0`, then `e ≥ 0`. -/
lemma e_nonneg (m : ℕ) (hm : ∀ i, (Qop M s μ)^[m] 1 i < 1)
    {e δ : Fin n → ℝ} (hδ : ∀ i, 0 ≤ δ i)
    (heq : ∀ i, e i = Qop M s μ e i + δ i) : ∀ i, 0 ≤ e i := by
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ := exists_rho M s μ m hm
  have hstep : ∀ i, Qop M s μ e i ≤ e i := fun i => by
    have := heq i; linarith [hδ i]
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ e ⟨s, Finset.mem_univ s⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨i, hi⟩ := hcon
  have hd : e i₁ < 0 := lt_of_le_of_lt (hi₁ i (Finset.mem_univ i)) hi
  have hne : ∀ j, (-e) j ≤ -e i₁ := fun j => by
    simp only [Pi.neg_apply]
    linarith [hi₁ j (Finset.mem_univ j)]
  have h1 : (Qop M s μ)^[m] (-e) i₁ ≤ (-e i₁) * ρ :=
    Qit_le_of_le M s μ m hρle (by linarith) hne i₁
  rw [Qit_neg] at h1
  simp only [Pi.neg_apply] at h1
  have h2 : (Qop M s μ)^[m] e i₁ ≤ e i₁ := Qit_le_self M s μ m hstep i₁
  nlinarith

end AC

namespace AC

variable {n : ℕ} {C : Type} [Fintype C]
variable (M : BertsekasSSPModel n C) (s : Fin n) (μ : Fin n → C)

lemma Pop_sub (e f : Fin n → ℝ) (i : Fin n) :
    Pop M μ (e - f) i = Pop M μ e i - Pop M μ f i := by
  simp [Pop, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Uniqueness of the evaluation pair `(λ_μ, h_μ)` normalized by `h(s) = 0`. -/
lemma eval_unique (m : ℕ) (hm : ∀ i, (Qop M s μ)^[m] 1 i < 1) (hμ : ∀ i, μ i ∈ M.U i)
    {lam lam' : ℝ} {h h' : Fin n → ℝ}
    (hns : h s = 0) (hns' : h' s = 0)
    (he : ∀ i, lam + h i = M.g i (μ i) + ∑ j, M.p i (μ i) j * h j)
    (he' : ∀ i, lam' + h' i = M.g i (μ i) + ∑ j, M.p i (μ i) j * h' j) :
    lam = lam' ∧ ∀ i, h i = h' i := by
  have hes : (h - h') s = 0 := by simp [hns, hns']
  have hQ : Qop M s μ (h - h') = Pop M μ (h - h') := Qop_eq_Pop M s μ hes
  have heq : ∀ i, (h - h') i = Qop M s μ (h - h') i + (0 : Fin n → ℝ) i - (lam - lam') := by
    intro i
    have h1 := he i
    have h2 := he' i
    have h3 : Qop M s μ (h - h') i = Pop M μ h i - Pop M μ h' i := by
      rw [hQ, Pop_sub]
    simp only [Pi.sub_apply, Pi.zero_apply]
    simp only [Pop] at h3
    rw [h3]
    linarith
  have hb1 : 0 ≤ lam - lam' :=
    beta_nonneg M s μ hμ hes (fun _ => le_refl 0) heq
  have hes' : (h' - h) s = 0 := by simp [hns, hns']
  have hQ' : Qop M s μ (h' - h) = Pop M μ (h' - h) := Qop_eq_Pop M s μ hes'
  have heq' : ∀ i, (h' - h) i = Qop M s μ (h' - h) i + (0 : Fin n → ℝ) i - (lam' - lam) := by
    intro i
    have h1 := he i
    have h2 := he' i
    have h3 : Qop M s μ (h' - h) i = Pop M μ h' i - Pop M μ h i := by
      rw [hQ', Pop_sub]
    simp only [Pi.sub_apply, Pi.zero_apply]
    simp only [Pop] at h3
    rw [h3]
    linarith
  have hb2 : 0 ≤ lam' - lam :=
    beta_nonneg M s μ hμ hes' (fun _ => le_refl 0) heq'
  have hlam : lam = lam' := by linarith
  refine ⟨hlam, ?_⟩
  have hfix : ∀ i, (h - h') i = Qop M s μ (h - h') i := by
    intro i
    have := heq i
    simp only [Pi.zero_apply] at this
    rw [this, hlam]
    ring
  have := eq_zero_of_fixed M s μ m hm hfix
  intro i
  have hi := this i
  simp only [Pi.sub_apply] at hi
  linarith

@[simp] lemma Qlin_apply (x : Fin n → ℝ) :
    (⟨⟨Qop M s μ, Qop_add M s μ⟩, fun c e => Qop_smul M s μ c e⟩ :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) x = Qop M s μ x := rfl

/-- `I - Q` is surjective: the evaluation system always has a solution. -/
lemma sub_Q_surjective (m : ℕ) (hm : ∀ i, (Qop M s μ)^[m] 1 i < 1) (g : Fin n → ℝ) :
    ∃ x : Fin n → ℝ, ∀ i, x i - Qop M s μ x i = g i := by
  set L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) -
      (⟨⟨Qop M s μ, Qop_add M s μ⟩, fun c e => Qop_smul M s μ c e⟩ :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hL
  have hLapp : ∀ x : Fin n → ℝ, ∀ i, L x i = x i - Qop M s μ x i := by
    intro x i
    simp [hL]
  have hinj : Function.Injective L := by
    intro x y hxy
    have hz : ∀ i, (x - y) i = Qop M s μ (x - y) i := by
      intro i
      have h1 : x i - Qop M s μ x i = y i - Qop M s μ y i := by
        rw [← hLapp x i, ← hLapp y i, hxy]
      have h2 : Qop M s μ (x - y) i = Qop M s μ x i - Qop M s μ y i := by
        rw [Qop_sub]; rfl
      simp only [Pi.sub_apply]
      rw [h2]
      linarith
    have hzero := eq_zero_of_fixed M s μ m hm hz
    funext i
    have := hzero i
    simp only [Pi.sub_apply] at this
    linarith
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨x, hx⟩ := hsurj g
  exact ⟨x, fun i => by rw [← hLapp x i, hx]⟩

/-- Existence of the evaluation pair for a stationary policy. -/
lemma exists_eval (m : ℕ) (hm : ∀ i, (Qop M s μ)^[m] 1 i < 1) (hμ : ∀ i, μ i ∈ M.U i) :
    ∃ (lam : ℝ) (h : Fin n → ℝ), h s = 0 ∧
      ∀ i, lam + h i = M.g i (μ i) + ∑ j, M.p i (μ i) j * h j := by
  obtain ⟨w, hw⟩ := sub_Q_surjective M s μ m hm (fun i => M.g i (μ i))
  obtain ⟨S, hS⟩ := sub_Q_surjective M s μ m hm 1
  have hS0 : ∀ i, 0 ≤ S i := by
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ S ⟨s, Finset.mem_univ s⟩
    intro i
    by_contra hcon
    push_neg at hcon
    have hd : S i₁ < 0 := lt_of_le_of_lt (hi₁ i (Finset.mem_univ i)) hcon
    have h1 : S i₁ * Qop M s μ 1 i₁ ≤ Qop M s μ S i₁ := by
      have h := Qop_mono M s μ (e := fun _ => S i₁) (f := S)
        (fun j => hi₁ j (Finset.mem_univ j)) i₁
      rwa [Qop_const] at h
    have h2 : S i₁ ≤ S i₁ * Qop M s μ 1 i₁ := by
      nlinarith [Qop_one_le M s μ hμ i₁]
    have h3 := hS i₁
    simp only [Pi.one_apply] at h3
    linarith
  have hSs : 1 ≤ S s := by
    have h3 := hS s
    simp only [Pi.one_apply] at h3
    have := Qop_nonneg M s μ hS0 s
    linarith
  refine ⟨w s / S s, fun i => w i - (w s / S s) * S i, ?_, ?_⟩
  · have hne : S s ≠ 0 := by linarith
    field_simp
    ring
  · intro i
    have hzero : (fun i => w i - (w s / S s) * S i) s = 0 := by
      have hne : S s ≠ 0 := by linarith
      simp only
      field_simp
      ring
    have hPQ : Qop M s μ (fun i => w i - (w s / S s) * S i)
        = Pop M μ (fun i => w i - (w s / S s) * S i) :=
      Qop_eq_Pop M s μ (e := fun i => w i - (w s / S s) * S i) hzero
    have hcomb : (fun i => w i - (w s / S s) * S i) = w - (w s / S s) • S := by
      funext j; simp [sub_eq_add_neg]
    have hQc : Qop M s μ (fun i => w i - (w s / S s) * S i) i
        = Qop M s μ w i - (w s / S s) * Qop M s μ S i := by
      rw [hcomb, Qop_sub, Qop_smul]
      simp
    have hPi : ∑ j, M.p i (μ i) j * (w j - (w s / S s) * S j)
        = Qop M s μ (fun i => w i - (w s / S s) * S i) i := by
      rw [hPQ]
      rfl
    rw [hPi, hQc]
    have h1 := hw i
    have h2 := hS i
    simp only [Pi.one_apply] at h2
    have hQw : Qop M s μ w i = w i - M.g i (μ i) := by linarith
    have hQS : Qop M s μ S i = S i - 1 := by linarith
    rw [hQw, hQS]
    dsimp only
    ring

end AC

open Finset in
theorem solution {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (s : Fin n)
    (hA : ∃ m : ℕ, 0 < m ∧ ∀ π, BertsekasSSPAdmissible M π →
      ∀ i, BertsekasSSPAvoidProb M s π m i < 1)
    (μ : ℕ → Fin n → C) (hadm : ∀ k i, μ k i ∈ M.U i)
    (lam : ℕ → ℝ) (h : ℕ → Fin n → ℝ)
    (heval : ∀ k i, lam k + h k i =
      M.g i (μ k i) + ∑ j, M.p i (μ k i) j * h k j)
    (hnorm : ∀ k, h k s = 0)
    (himp : ∀ k i,
      M.g i (μ (k + 1) i) + ∑ j, M.p i (μ (k + 1) i) j * h k j =
        BertsekasSSPBellmanOp M (h k) i) :
    (∀ k, lam (k + 1) ≤ lam k) ∧
    (∀ k, lam (k + 1) = lam k → ∀ i, h (k + 1) i ≤ h k i) ∧
    (∃ k, ∀ i, lam k + h k i = BertsekasSSPBellmanOp M (h k) i) := by
  classical
  obtain ⟨m, hm0, hmA⟩ := hA
  have hmQ : ∀ k, ∀ i, (AC.Qop M s (μ k))^[m] 1 i < 1 := by
    intro k i
    have hadm' : BertsekasSSPAdmissible M (fun _ => μ k) := fun _ i => hadm k i
    have hlt := hmA _ hadm' i
    rwa [AC.avoid_eq] at hlt
  set δ : ℕ → Fin n → ℝ :=
    fun k i => lam k + h k i - BertsekasSSPBellmanOp M (h k) i with hδdef
  have hδ0 : ∀ k i, 0 ≤ δ k i := by
    intro k i
    have h1 : BertsekasSSPBellmanOp M (h k) i ≤
        M.g i (μ k i) + ∑ j, M.p i (μ k i) j * h k j :=
      Finset.inf'_le _ (hadm k i)
    have h2 := heval k i
    simp only [hδdef]
    linarith
  have hes : ∀ k, (h k - h (k + 1)) s = 0 := by
    intro k; simp [hnorm]
  have hrel : ∀ k i, (h k - h (k + 1)) i
      = AC.Qop M s (μ (k + 1)) (h k - h (k + 1)) i + δ k i - (lam k - lam (k + 1)) := by
    intro k i
    have hQ : AC.Qop M s (μ (k + 1)) (h k - h (k + 1))
        = AC.Pop M (μ (k + 1)) (h k - h (k + 1)) := AC.Qop_eq_Pop M s _ (hes k)
    have h3 : AC.Qop M s (μ (k + 1)) (h k - h (k + 1)) i
        = (∑ j, M.p i (μ (k + 1) i) j * h k j)
          - (∑ j, M.p i (μ (k + 1) i) j * h (k + 1) j) := by
      rw [hQ, AC.Pop_sub]; rfl
    have e1 := heval (k + 1) i
    have e2 := himp k i
    simp only [Pi.sub_apply, hδdef]
    rw [h3]
    linarith
  have hpart1 : ∀ k, lam (k + 1) ≤ lam k := by
    intro k
    have hb := AC.beta_nonneg M s (μ (k + 1)) (fun i => hadm (k + 1) i) (hes k)
      (fun i => hδ0 k i) (hrel k)
    linarith
  have hpart2 : ∀ k, lam (k + 1) = lam k → ∀ i, h (k + 1) i ≤ h k i := by
    intro k hlam i
    have hrel' : ∀ i, (h k - h (k + 1)) i
        = AC.Qop M s (μ (k + 1)) (h k - h (k + 1)) i + δ k i := by
      intro i
      have hi := hrel k i
      rw [hlam] at hi
      linarith
    have hnn := AC.e_nonneg M s (μ (k + 1)) m (hmQ (k + 1)) (fun i => hδ0 k i) hrel' i
    simp only [Pi.sub_apply] at hnn
    linarith
  refine ⟨hpart1, hpart2, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hδne : ∀ k, ∃ i, 0 < δ k i := by
    intro k
    obtain ⟨i, hi⟩ := hcon k
    refine ⟨i, lt_of_le_of_ne (hδ0 k i) (fun hh => hi ?_)⟩
    simp only [hδdef] at hh
    linarith
  have hstep : ∀ k, lam (k + 1) < lam k ∨
      (lam (k + 1) = lam k ∧ (∀ i, h (k + 1) i ≤ h k i) ∧ h (k + 1) ≠ h k) := by
    intro k
    rcases lt_or_eq_of_le (hpart1 k) with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, hpart2 k heq, ?_⟩
      intro hcontra
      obtain ⟨i, hi⟩ := hδne k
      have hrel' := hrel k i
      rw [heq] at hrel'
      have hzero : (h k - h (k + 1)) = 0 := by rw [hcontra]; simp
      rw [hzero] at hrel'
      simp only [Pi.zero_apply, AC.Qop] at hrel'
      simp at hrel'
      linarith
  have hLt : ∀ a b, a < b → (lam b < lam a ∨
      (lam b = lam a ∧ (∀ i, h b i ≤ h a i) ∧ h b ≠ h a)) := by
    intro a b hab
    induction b with
    | zero => omega
    | succ b ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hlt | heqb
        · have h1 := ih hlt
          have h2 := hstep b
          rcases h1 with h1 | ⟨h1e, h1le, h1ne⟩
          · rcases h2 with h2 | ⟨h2e, -, -⟩
            · exact Or.inl (lt_trans h2 h1)
            · exact Or.inl (by linarith)
          · rcases h2 with h2 | ⟨h2e, h2le, h2ne⟩
            · exact Or.inl (by linarith)
            · refine Or.inr ⟨by linarith, fun i => le_trans (h2le i) (h1le i), ?_⟩
              intro hcontra
              apply h1ne
              funext i
              have hbi : h b i ≤ h a i := h1le i
              have hb1i : h (b + 1) i ≤ h b i := h2le i
              have : h (b + 1) i = h a i := by rw [hcontra]
              linarith
        · subst heqb; exact hstep a
  have hnoteq : ∀ a b, a < b → μ a ≠ μ b := by
    intro a b hab hμab
    have hevala : ∀ i, lam a + h a i =
        M.g i (μ b i) + ∑ j, M.p i (μ b i) j * h a j := by
      intro i; rw [← hμab]; exact heval a i
    have huniq := AC.eval_unique M s (μ b) m (hmQ b) (fun i => hadm b i)
      (hnorm a) (hnorm b) hevala (heval b)
    rcases hLt a b hab with hl | ⟨hle, -, hne⟩
    · linarith [huniq.1]
    · exact hne (funext fun i => (huniq.2 i).symm)
  obtain ⟨a, b, hab, hμab⟩ := Finite.exists_ne_map_eq_of_infinite μ
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hnoteq a b hlt hμab
  · exact hnoteq b a (lt_of_le_of_ne hge (fun hh => hab hh.symm)) hμab.symm
