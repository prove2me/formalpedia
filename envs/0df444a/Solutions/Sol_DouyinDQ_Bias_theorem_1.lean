-- Prove2me | solution 1 for DouyinDQ.Bias.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:46:12.418453+00:00
-- url     : https://prove2.me/submissions/a69a3f8c-17f4-4405-a7d7-dc0f931799b7

import Theorems.Thm_DouyinDQ_Bias_path_value
import Theorems.Thm_DouyinDQ_Bias_k1_identity
import Theorems.Thm_DouyinDQ_Bias_corollary_1
import Definitions.Def_DouyinDQ_Bias_Model

open Matrix Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DouyinDQ.Bias

section Infra

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- Fundamental-matrix operator: `Σ_t P_π^t g`. -/
noncomputable def dqN (M : MDP S A) (π : S → A → ℝ) (g : S → ℝ) (s : S) : ℝ :=
  ∑' t : ℕ, (Ppol M π ^ t *ᵥ g) s

/-- Mass outside the absorbing class at time `t`. -/
noncomputable def dqm (M : MDP S A) (π : S → A → ℝ) (Sabs : Set S)
    [DecidablePred (· ∈ Sabs)] (t : ℕ) (s : S) : ℝ :=
  ∑ s' : S, if s' ∈ Sabs then 0 else (Ppol M π ^ t) s s'

lemma dq_ppol_nonneg (M : MDP S A) (hM : M.Standing) (π : S → A → ℝ)
    (hπ : ∀ s a, 0 ≤ π s a) (s s' : S) : 0 ≤ Ppol M π s s' := by
  unfold Ppol
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hπ s a) (hM.1 a s s')

lemma dq_pow_nonneg (P : Matrix S S ℝ) (hP : ∀ i j, 0 ≤ P i j) (t : ℕ) :
    ∀ i j, 0 ≤ (P ^ t) i j := by
  induction t with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun u _ => mul_nonneg (ih i u) (hP u j)

lemma dq_pow_closed (Sabs : Set S) (P : Matrix S S ℝ)
    (hcl : ∀ s ∈ Sabs, ∀ s' ∉ Sabs, P s s' = 0) (t : ℕ) :
    ∀ s ∈ Sabs, ∀ s' ∉ Sabs, (P ^ t) s s' = 0 := by
  induction t with
  | zero =>
    intro s hs s' hs'
    have : s ≠ s' := fun h => hs' (h ▸ hs)
    simp [Matrix.one_apply, this]
  | succ t ih =>
    intro s hs s' hs'
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases hu : u ∈ Sabs
    · rw [hcl u hu s' hs', mul_zero]
    · rw [ih s hs u hu, zero_mul]

lemma dq_mulVec_V0 (Sabs : Set S) (P : Matrix S S ℝ)
    (hcl : ∀ s ∈ Sabs, ∀ s' ∉ Sabs, P s s' = 0) (g : S → ℝ)
    (hg : ∀ s ∈ Sabs, g s = 0) : ∀ s ∈ Sabs, (P *ᵥ g) s = 0 := by
  intro s hs
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : u ∈ Sabs
  · rw [hg u hu, mul_zero]
  · rw [hcl s hs u hu, zero_mul]

lemma dq_abs_le_sum (g : S → ℝ) (u : S) : |g u| ≤ ∑ v, |g v| :=
  Finset.single_le_sum (f := fun v => |g v|) (fun v _ => abs_nonneg _) (Finset.mem_univ u)

/-- Pointwise bound of `Q *ᵥ g` for a nonnegative matrix and `g` vanishing on `Sabs`. -/
lemma dq_mulVec_bound (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (B : ℝ)
    (hB : ∀ s, |g s| ≤ B) (s : S) :
    |(Q *ᵥ g) s| ≤ B * ∑ s' : S, if s' ∈ Sabs then 0 else Q s s' := by
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  by_cases hu : u ∈ Sabs
  · simp [hu, hg u hu]
  · simp only [hu, if_false, abs_mul, abs_of_nonneg (hQ s u)]
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB u) (hQ s u)

variable (M : MDP S A) (hM : M.Standing) (Sabs : Set S) [DecidablePred (· ∈ Sabs)]
  (π : S → A → ℝ)

include hM

lemma dq_summable (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (s : S) :
    Summable (fun t : ℕ => (Ppol M π ^ t *ᵥ g) s) := by
  obtain ⟨x, hx, -⟩ := ht s
  refine Summable.of_norm_bounded (hx.summable.mul_left (∑ v, |g v|)) fun t => ?_
  rw [Real.norm_eq_abs]
  exact dq_mulVec_bound Sabs _ (dq_pow_nonneg _ (dq_ppol_nonneg M hM π hπ) t) g hg _
    (dq_abs_le_sum g) s

lemma dq_hasSum (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (s : S) :
    HasSum (fun t : ℕ => (Ppol M π ^ t *ᵥ g) s) (dqN M π g s) :=
  (dq_summable M hM Sabs π hπ T ht g hg s).hasSum

/-- `|N g| ≤ B T`. -/
lemma dq_N_bound (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ s, |g s| ≤ B) (s : S) : |dqN M π g s| ≤ B * T := by
  obtain ⟨x, hx, hxT⟩ := ht s
  have hb := fun t => dq_mulVec_bound Sabs _ (dq_pow_nonneg _ (dq_ppol_nonneg M hM π hπ) t)
    g hg B hB s
  have h1 : dqN M π g s ≤ B * x :=
    hasSum_le (fun t => (le_abs_self _).trans (hb t)) (dq_hasSum M hM Sabs π hπ T ht g hg s)
      (hx.mul_left B)
  have h2 : -(B * x) ≤ dqN M π g s := by
    have := hasSum_le (fun t => (neg_le.mpr ((neg_le_abs _).trans (hb t))))
      (hx.mul_left B).neg (dq_hasSum M hM Sabs π hπ T ht g hg s)
    simpa using this
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

lemma dq_N_V0 (hcl : ∀ s ∈ Sabs, ∀ s' ∉ Sabs, Ppol M π s s' = 0)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) : ∀ s ∈ Sabs, dqN M π g s = 0 := by
  intro s hs
  unfold dqN
  have : ∀ t : ℕ, (Ppol M π ^ t *ᵥ g) s = 0 := fun t =>
    dq_mulVec_V0 Sabs _ (dq_pow_closed Sabs _ hcl t) g hg s hs
  simp [this]

/-- `Σ_t (Q P^t g) = Q (N g)`. -/
lemma dq_tsum_mulVec (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (Q : Matrix S S ℝ) (s : S) :
    HasSum (fun t : ℕ => ((Q * Ppol M π ^ t) *ᵥ g) s) ((Q *ᵥ dqN M π g) s) := by
  have : (fun t : ℕ => ((Q * Ppol M π ^ t) *ᵥ g) s) =
      fun t => ∑ u, Q s u * (Ppol M π ^ t *ᵥ g) u := by
    funext t
    rw [← Matrix.mulVec_mulVec]
    rfl
  rw [this]
  simp only [Matrix.mulVec, dotProduct]
  exact hasSum_sum fun u _ => (dq_hasSum M hM Sabs π hπ T ht g hg u).mul_left (Q s u)

lemma dq_N_fixed (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (s : S) :
    dqN M π g s = g s + (Ppol M π *ᵥ dqN M π g) s := by
  rw [← (dq_tsum_mulVec M hM Sabs π hπ T ht g hg (Ppol M π) s).tsum_eq]
  rw [show dqN M π g s = ∑' t : ℕ, (Ppol M π ^ t *ᵥ g) s from rfl,
    (dq_summable M hM Sabs π hπ T ht g hg s).tsum_eq_zero_add]
  simp [pow_succ']

lemma dq_N_shift (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (hcl : ∀ s ∈ Sabs, ∀ s' ∉ Sabs, Ppol M π s s' = 0)
    (u : S → ℝ) (hu : ∀ s ∈ Sabs, u s = 0) (s : S) :
    dqN M π (Ppol M π *ᵥ u) s = dqN M π u s - u s := by
  have h1 := dq_N_fixed M hM Sabs π hπ T ht u hu s
  have h2 : dqN M π (Ppol M π *ᵥ u) s = (Ppol M π *ᵥ dqN M π u) s := by
    show ∑' t : ℕ, (Ppol M π ^ t *ᵥ (Ppol M π *ᵥ u)) s = _
    rw [← (dq_tsum_mulVec M hM Sabs π hπ T ht u hu (Ppol M π) s).tsum_eq]
    congr 1
    funext t
    rw [Matrix.mulVec_mulVec, ← pow_succ, pow_succ']
  linarith

lemma dq_N_sub (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g h : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (hh : ∀ s ∈ Sabs, h s = 0) (s : S) :
    dqN M π (g - h) s = dqN M π g s - dqN M π h s := by
  have := (dq_hasSum M hM Sabs π hπ T ht g hg s).sub (dq_hasSum M hM Sabs π hπ T ht h hh s)
  rw [← this.tsum_eq]
  unfold dqN
  congr 1
  funext t
  rw [Matrix.mulVec_sub]
  rfl

lemma dq_N_add (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g h : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (hh : ∀ s ∈ Sabs, h s = 0) (s : S) :
    dqN M π (g + h) s = dqN M π g s + dqN M π h s := by
  have := (dq_hasSum M hM Sabs π hπ T ht g hg s).add (dq_hasSum M hM Sabs π hπ T ht h hh s)
  rw [← this.tsum_eq]
  unfold dqN
  congr 1
  funext t
  rw [Matrix.mulVec_add]
  rfl

lemma dq_Etilde_hasSum (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) :
    HasSum (fun t : ℕ => ∑ s : S, M.ρ s * (Ppol M π ^ t *ᵥ g) s)
      (∑ s, M.ρ s * dqN M π g s) :=
  hasSum_sum fun s _ => (dq_hasSum M hM Sabs π hπ T ht g hg s).mul_left (M.ρ s)

lemma dq_Etilde_eq (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) :
    Etilde M π g = ∑ s, M.ρ s * dqN M π g s :=
  (dq_Etilde_hasSum M hM Sabs π hπ T ht g hg).tsum_eq

omit hM in
lemma dq_N_smul (c : ℝ) (g : S → ℝ) (s : S) : dqN M π (c • g) s = c * dqN M π g s := by
  unfold dqN
  rw [← tsum_mul_left]
  congr 1
  funext t
  rw [Matrix.mulVec_smul]
  rfl

lemma dq_Etilde_sub (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g h : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (hh : ∀ s ∈ Sabs, h s = 0) :
    Etilde M π g - Etilde M π h = Etilde M π (g - h) := by
  have hgh : ∀ s ∈ Sabs, (g - h) s = 0 := fun s hs => by simp [hg s hs, hh s hs]
  rw [dq_Etilde_eq M hM Sabs π hπ T ht g hg, dq_Etilde_eq M hM Sabs π hπ T ht h hh,
    dq_Etilde_eq M hM Sabs π hπ T ht _ hgh, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dq_N_sub M hM Sabs π hπ T ht g h hg hh s]
  ring

lemma dq_Etilde_add (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g h : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (hh : ∀ s ∈ Sabs, h s = 0) :
    Etilde M π g + Etilde M π h = Etilde M π (g + h) := by
  have hgh : ∀ s ∈ Sabs, (g + h) s = 0 := fun s hs => by simp [hg s hs, hh s hs]
  rw [dq_Etilde_eq M hM Sabs π hπ T ht g hg, dq_Etilde_eq M hM Sabs π hπ T ht h hh,
    dq_Etilde_eq M hM Sabs π hπ T ht _ hgh, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dq_N_add M hM Sabs π hπ T ht g h hg hh s]
  ring


lemma dq_Qfun (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (a : A) (s : S) :
    Qfun M π a g s = g s + (M.P a *ᵥ dqN M π g) s := by
  unfold Qfun
  rw [(dq_tsum_mulVec M hM Sabs π hπ T ht g hg (M.P a) s).tsum_eq]

omit hM in
lemma dq_ppol_mulVec (π' : S → A → ℝ) (v : S → ℝ) (s : S) :
    (Ppol M π' *ᵥ v) s = ∑ a, π' s a * (M.P a *ᵥ v) s := by
  simp only [Matrix.mulVec, dotProduct, Ppol, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun u _ => by ring

lemma dq_DQ_succ (π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (T : ℝ)
    (ht : AbsTimeLT M Sabs π T) (k : ℕ) (hk : ∀ s ∈ Sabs, DQ M π π' k s = 0) (s : S) :
    DQ M π π' (k + 1) s = (Ppol M π' *ᵥ dqN M π (DQ M π π' k)) s -
      (Ppol M π *ᵥ dqN M π (DQ M π π' k)) s := by
  simp only [DQ]
  simp only [dq_Qfun M hM Sabs π hπ.1 T ht _ hk, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, hπ'.2 s, hπ.2 s, dq_ppol_mulVec]
  ring

lemma dq_DQ_V0 (π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (T : ℝ)
    (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T)
    (habs' : IsAbsorbingFor M Sabs π') :
    ∀ k, ∀ s ∈ Sabs, DQ M π π' k s = 0 := by
  intro k
  induction k with
  | zero => intro s hs; simp [DQ, rpol, habs'.2 s hs]
  | succ k ih =>
    intro s hs
    rw [dq_DQ_succ M hM Sabs π π' hπ hπ' T ht k ih s]
    have hN := dq_N_V0 M hM Sabs π habs.1 _ ih
    rw [dq_mulVec_V0 Sabs _ habs'.1 _ hN s hs, dq_mulVec_V0 Sabs _ habs.1 _ hN s hs, sub_zero]

/-- One step of the policy expansion. -/
lemma dq_step (π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (T : ℝ)
    (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T)
    (habs' : IsAbsorbingFor M Sabs π') (ht' : AbsTimeLT M Sabs π' T)
    (h : S → ℝ) (hh : ∀ s ∈ Sabs, h s = 0) :
    Etilde M π' h = Etilde M π h +
      Etilde M π' (fun s => (Ppol M π' *ᵥ dqN M π h) s - (Ppol M π *ᵥ dqN M π h) s) := by
  set u := dqN M π h with hu_def
  have hu : ∀ s ∈ Sabs, u s = 0 := dq_N_V0 M hM Sabs π habs.1 h hh
  have hP'u : ∀ s ∈ Sabs, (Ppol M π' *ᵥ u) s = 0 := dq_mulVec_V0 Sabs _ habs'.1 u hu
  have hPu : ∀ s ∈ Sabs, (Ppol M π *ᵥ u) s = 0 := dq_mulVec_V0 Sabs _ habs.1 u hu
  have hfix : (Ppol M π *ᵥ u) = u - h := by
    funext s
    have := dq_N_fixed M hM Sabs π hπ.1 T ht h hh s
    simp only [Pi.sub_apply]
    rw [← hu_def] at this
    linarith
  have hD : (fun s => (Ppol M π' *ᵥ u) s - (Ppol M π *ᵥ u) s) =
      (Ppol M π' *ᵥ u) - (Ppol M π *ᵥ u) := rfl
  have hDV : ∀ s ∈ Sabs, (fun s => (Ppol M π' *ᵥ u) s - (Ppol M π *ᵥ u) s) s = 0 := by
    intro s hs; simp [hP'u s hs, hPu s hs]
  rw [dq_Etilde_eq M hM Sabs π' hπ'.1 T ht' h hh, dq_Etilde_eq M hM Sabs π hπ.1 T ht h hh,
    dq_Etilde_eq M hM Sabs π' hπ'.1 T ht' _ hDV, hD]
  have key : ∀ s, dqN M π' ((Ppol M π' *ᵥ u) - (Ppol M π *ᵥ u)) s =
      dqN M π' h s - u s := by
    intro s
    rw [dq_N_sub M hM Sabs π' hπ'.1 T ht' _ _ hP'u hPu,
      dq_N_shift M hM Sabs π' hπ'.1 T ht' habs'.1 u hu, hfix]
    have hsub := dq_N_sub M hM Sabs π' hπ'.1 T ht' u h hu hh s
    rw [hsub]
    ring
  simp only [key, mul_sub, Finset.sum_sub_distrib]
  ring

lemma dq_step_DQ (π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (T : ℝ)
    (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T)
    (habs' : IsAbsorbingFor M Sabs π') (ht' : AbsTimeLT M Sabs π' T) (k : ℕ) :
    Etilde M π' (DQ M π π' k) = Etilde M π (DQ M π π' k) +
      Etilde M π' (DQ M π π' (k + 1)) := by
  have hk := dq_DQ_V0 M hM Sabs π π' hπ hπ' T habs ht habs' k
  rw [dq_step M hM Sabs π π' hπ hπ' T habs ht habs' ht' _ hk]
  congr 2
  funext s
  rw [dq_DQ_succ M hM Sabs π π' hπ hπ' T ht k hk s]

theorem dq_theorem_2 (π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (T : ℝ)
    (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T)
    (habs' : IsAbsorbingFor M Sabs π') (ht' : AbsTimeLT M Sabs π' T) (K : ℕ) :
    Etilde M π' (rpol M π') =
      (∑ k ∈ Finset.range (K + 1), Etilde M π (DQ M π π' k)) +
        Etilde M π' (DQ M π π' (K + 1)) := by
  induction K with
  | zero =>
    rw [show rpol M π' = DQ M π π' 0 from rfl]
    simpa using dq_step_DQ M hM Sabs π π' hπ hπ' T habs ht habs' ht' 0
  | succ K ih =>
    rw [ih, dq_step_DQ M hM Sabs π π' hπ hπ' T habs ht habs' ht' (K + 1),
      Finset.sum_range_succ _ (K + 1)]
    ring

lemma dq_T_nonneg (T : ℝ) (ht : AbsTimeLT M Sabs π T) (hπ : ∀ s a, 0 ≤ π s a) : 0 ≤ T := by
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hM.2.2.2
    simp at this
  obtain ⟨s⟩ := hne
  obtain ⟨x, hx, hxT⟩ := ht s
  have : 0 ≤ x := hx.nonneg fun t => Finset.sum_nonneg fun s' _ => by
    split_ifs
    · exact le_refl 0
    · exact dq_pow_nonneg _ (dq_ppol_nonneg M hM π hπ) t s s'
  linarith

/-- `|Ẽ h| ≤ B T`. -/
lemma dq_Etilde_bound (hπ : ∀ s a, 0 ≤ π s a) (T : ℝ) (ht : AbsTimeLT M Sabs π T)
    (g : S → ℝ) (hg : ∀ s ∈ Sabs, g s = 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ s, |g s| ≤ B) : |Etilde M π g| ≤ B * T := by
  rw [dq_Etilde_eq M hM Sabs π hπ T ht g hg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ s, |M.ρ s * dqN M π g s| ≤ ∑ s, M.ρ s * (B * T) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (hM.2.2.1 s)]
        exact mul_le_mul_of_nonneg_left (dq_N_bound M hM Sabs π hπ T ht g hg B hB0 hB s)
          (hM.2.2.1 s)
    _ = B * T := by rw [← Finset.sum_mul, hM.2.2.2, one_mul]

lemma dq_DQ_bound (π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (T δ : ℝ)
    (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T)
    (habs' : IsAbsorbingFor M Sabs π')
    (hδ : ∀ s, ∑ s', |Ppol M π s s' - Ppol M π' s s'| ≤ δ) (R : ℝ)
    (hR : ∀ s, |rpol M π' s| ≤ R) :
    ∀ k s, |DQ M π π' k s| ≤ (δ * T) ^ k * R := by
  have hT := dq_T_nonneg M hM Sabs π T ht hπ.1
  have hR0 : 0 ≤ R := by
    have hne : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := hM.2.2.2
      simp at this
    obtain ⟨s⟩ := hne
    exact (abs_nonneg _).trans (hR s)
  have hδ0 : 0 ≤ δ := by
    have hne : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := hM.2.2.2
      simp at this
    obtain ⟨s⟩ := hne
    exact (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hδ s)
  intro k
  induction k with
  | zero => intro s; show |rpol M π' s| ≤ (δ * T) ^ 0 * R; simpa using hR s
  | succ k ih =>
    intro s
    have hk := dq_DQ_V0 M hM Sabs π π' hπ hπ' T habs ht habs' k
    rw [dq_DQ_succ M hM Sabs π π' hπ hπ' T ht k hk s]
    have hB0 : 0 ≤ (δ * T) ^ k * R := mul_nonneg (pow_nonneg (mul_nonneg hδ0 hT) k) hR0
    have hN := dq_N_bound M hM Sabs π hπ.1 T ht _ hk _ hB0 ih
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← sub_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w, |(Ppol M π' s w - Ppol M π s w) * dqN M π (DQ M π π' k) w|
        ≤ ∑ w, |Ppol M π s w - Ppol M π' s w| * ((δ * T) ^ k * R * T) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (hN w) (abs_nonneg _)
      _ ≤ δ * ((δ * T) ^ k * R * T) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hδ s) (mul_nonneg hB0 hT)
      _ = (δ * T) ^ (k + 1) * R := by ring

theorem dq_corollary_1 (π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (T δ : ℝ)
    (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T)
    (habs' : IsAbsorbingFor M Sabs π') (ht' : AbsTimeLT M Sabs π' T)
    (hδ : ∀ s, ∑ s', |Ppol M π s s' - Ppol M π' s s'| ≤ δ) (K : ℕ) (R : ℝ)
    (hR : ∀ s, |rpol M π' s| ≤ R) :
    |Etilde M π' (rpol M π') -
      ∑ k ∈ Finset.range (K + 1), Etilde M π (DQ M π π' k)| ≤
      (δ * T) ^ (K + 1) * T * R := by
  rw [dq_theorem_2 M hM Sabs π π' hπ hπ' T habs ht habs' ht' K]
  have hT := dq_T_nonneg M hM Sabs π T ht hπ.1
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hM.2.2.2
    simp at this
  have hb := dq_DQ_bound M hM Sabs π π' hπ hπ' T δ habs ht habs' hδ R hR (K + 1)
  have hB0 : 0 ≤ (δ * T) ^ (K + 1) * R := (abs_nonneg _).trans (hb (Classical.arbitrary S))
  have := dq_Etilde_bound M hM Sabs π' hπ'.1 T ht' _
    (dq_DQ_V0 M hM Sabs π π' hπ hπ' T habs ht habs' (K + 1)) _ hB0 hb
  calc _ = |Etilde M π' (DQ M π π' (K + 1))| := by ring_nf
    _ ≤ _ := this
    _ = _ := by ring


end Infra

section Paths

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  (M : MDP S A) (π : S → A → ℝ)

/-- One-step backward kernel on state-action functions. -/
noncomputable def dqK (f : S × A → ℝ) (p : S × A) : ℝ :=
  ∑ s', M.P p.2 p.1 s' * ∑ a', π s' a' * f (s', a')

/-- Policy averaging of a state-action function. -/
noncomputable def dqPi (h : S × A → ℝ) (s : S) : ℝ := ∑ a, π s a * h (s, a)

lemma dq_pathWeight_snoc (H : ℕ) (ω : Fin (H + 1) → S × A) (x : S × A) :
    pathWeight M π (H + 1) (Fin.snoc ω x) = pathWeight M π H ω *
      (π x.1 x.2 * M.P (ω (Fin.last H)).2 (ω (Fin.last H)).1 x.1) := by
  have h0 : (Fin.snoc ω x : Fin (H + 2) → S × A) 0 = ω 0 := by
    rw [show (0 : Fin (H + 2)) = Fin.castSucc (0 : Fin (H + 1)) from rfl, Fin.snoc_castSucc]
  have e1 : ∏ t : Fin (H + 2), π ((Fin.snoc ω x : Fin (H + 2) → S × A) t).1
      ((Fin.snoc ω x : Fin (H + 2) → S × A) t).2 =
      (∏ t : Fin (H + 1), π (ω t).1 (ω t).2) * π x.1 x.2 := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have e2 : ∏ t : Fin (H + 1), M.P ((Fin.snoc ω x : Fin (H + 2) → S × A) t.castSucc).2
      ((Fin.snoc ω x : Fin (H + 2) → S × A) t.castSucc).1
      ((Fin.snoc ω x : Fin (H + 2) → S × A) t.succ).1 =
      (∏ t : Fin H, M.P (ω t.castSucc).2 (ω t.castSucc).1 (ω t.succ).1) *
        M.P (ω (Fin.last H)).2 (ω (Fin.last H)).1 x.1 := by
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun t _ => ?_
      rw [Fin.succ_castSucc]
      simp only [Fin.snoc_castSucc]
    · rw [Fin.succ_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
  unfold pathWeight
  rw [e1, e2, h0]
  ring

lemma dq_sum_snoc (H : ℕ) (F : (Fin (H + 2) → S × A) → ℝ) :
    ∑ ω', F ω' = ∑ ω : Fin (H + 1) → S × A, ∑ x : S × A, F (Fin.snoc ω x) := by
  rw [← (Fin.snocEquiv (fun _ => S × A)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma dq_pathExp_step (H : ℕ) (G : (Fin (H + 1) → S × A) → ℝ) (f : S × A → ℝ) :
    pathExp M π (H + 1) (fun ω' => G (Fin.init ω') * f (ω' (Fin.last (H + 1)))) =
      pathExp M π H (fun ω => G ω * dqK M π f (ω (Fin.last H))) := by
  unfold pathExp
  rw [dq_sum_snoc]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Fin.init_snoc, Fin.snoc_last, dq_pathWeight_snoc, dqK]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun a' _ => by ring

lemma dq_Pi_K (f : S × A → ℝ) (s : S) :
    dqPi π (dqK M π f) s = (Ppol M π *ᵥ dqPi π f) s := by
  simp only [dqPi, dqK, Matrix.mulVec, dotProduct, Ppol]
  calc ∑ a, π s a * ∑ s', M.P a s s' * ∑ a', π s' a' * f (s', a')
      = ∑ a, ∑ s', π s a * M.P a s s' * ∑ a', π s' a' * f (s', a') := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => by ring
    _ = ∑ s', ∑ a, π s a * M.P a s s' * ∑ a', π s' a' * f (s', a') := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [Finset.sum_mul]

lemma dq_pathExp_zero (F : (Fin 1 → S × A) → ℝ) :
    pathExp M π 0 F = ∑ s, M.ρ s * ∑ a, π s a * F (fun _ => (s, a)) := by
  unfold pathExp
  rw [← (Equiv.funUnique (Fin 1) (S × A)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
  simp [pathWeight, Equiv.funUnique]
  rw [mul_assoc]
  rfl

lemma dq_pathExp_last (t : ℕ) : ∀ h : S × A → ℝ,
    pathExp M π t (fun ω => h (ω (Fin.last t))) =
      ∑ s, M.ρ s * (Ppol M π ^ t *ᵥ dqPi π h) s := by
  induction t with
  | zero =>
    intro h
    rw [dq_pathExp_zero]
    simp [dqPi]
  | succ t ih =>
    intro h
    have := dq_pathExp_step M π t (fun _ => 1) h
    simp only [one_mul] at this
    rw [this, ih]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    have : dqPi π (dqK M π h) = Ppol M π *ᵥ dqPi π h := funext (dq_Pi_K M π h)
    rw [this, Matrix.mulVec_mulVec, ← pow_succ]

theorem dq_path_value (hM : M.Standing) (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (T : ℝ)
    (hπ : IsPolicy π) (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T) :
    HasSum (fun t : ℕ => pathExp M π t
      (fun ω => M.r (ω (Fin.last t)).1 (ω (Fin.last t)).2))
      (Etilde M π (rpol M π)) := by
  have hr : ∀ s ∈ Sabs, rpol M π s = 0 := fun s hs => by simp [rpol, habs.2 s hs]
  rw [dq_Etilde_eq M hM Sabs π hπ.1 T ht _ hr]
  have := dq_Etilde_hasSum M hM Sabs π hπ.1 T ht _ hr
  convert this using 2 with t
  exact dq_pathExp_last M π t (fun p => M.r p.1 p.2)


lemma dq_K_one (hM : M.Standing) (hπ : IsPolicy π) (p : S × A) :
    dqK M π (fun _ => 1) p = 1 := by
  simp only [dqK, mul_one, hπ.2, hM.2.1]

lemma dq_pathExp_prefix (n : ℕ) (F : (Fin (n + 1) → S × A) → ℝ) (hM : M.Standing)
    (hπ : IsPolicy π) : ∀ d : ℕ,
    pathExp M π (n + d) (fun ω => F (fun i => ω (Fin.castLE (by omega) i))) =
      pathExp M π n F := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    have := dq_pathExp_step M π (n + d)
      (fun ω => F (fun i => ω (Fin.castLE (by omega) i))) (fun _ => 1)
    simp only [mul_one, dq_K_one M π hM hπ] at this
    rw [← ih, ← this]
    rfl

lemma dq_pathExp_two (t : ℕ) (g : S × A → ℝ) : ∀ (j : ℕ) (f : S × A → ℝ),
    pathExp M π (t + j) (fun ω => g (ω ⟨t, by omega⟩) * f (ω (Fin.last (t + j)))) =
      pathExp M π t (fun ω => g (ω (Fin.last t)) * (dqK M π)^[j] f (ω (Fin.last t))) := by
  intro j
  induction j with
  | zero => intro f; rfl
  | succ j ih =>
    intro f
    have := dq_pathExp_step M π (t + j) (fun ω => g (ω ⟨t, by omega⟩)) f
    rw [Function.iterate_succ_apply, ← ih (dqK M π f), ← this]
    rfl

lemma dq_pathExp_pair (hM : M.Standing) (hπ : IsPolicy π) (g f : S × A → ℝ)
    (H t t' : ℕ) (ht : t < H + 1) (ht' : t' < H + 1) (hle : t ≤ t') :
    pathExp M π H (fun ω => g (ω ⟨t, ht⟩) * f (ω ⟨t', ht'⟩)) =
      ∑ s, M.ρ s * (Ppol M π ^ t *ᵥ dqPi π (fun p => g p * (dqK M π)^[t' - t] f p)) s := by
  obtain ⟨j, rfl⟩ : ∃ j, t' = t + j := ⟨t' - t, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, H = t + j + d := ⟨H - (t + j), by omega⟩
  have h1 := dq_pathExp_prefix M π (t + j)
    (fun ω => g (ω ⟨t, by omega⟩) * f (ω (Fin.last (t + j)))) hM hπ d
  rw [show t + j - t = j by omega]
  rw [← dq_pathExp_last M π t (fun p => g p * (dqK M π)^[j] f p), ← dq_pathExp_two M π t g j f,
    ← h1]
  rfl

lemma dq_pathExp_sum {H : ℕ} {ι : Type} (s : Finset ι)
    (F : ι → (Fin (H + 1) → S × A) → ℝ) :
    pathExp M π H (fun ω => ∑ i ∈ s, F i ω) = ∑ i ∈ s, pathExp M π H (F i) := by
  unfold pathExp
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma dq_Pi_iterK (f : S × A → ℝ) : ∀ j : ℕ,
    dqPi π ((dqK M π)^[j] f) = Ppol M π ^ j *ᵥ dqPi π f := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', funext (dq_Pi_K M π _), ih, Matrix.mulVec_mulVec,
      ← pow_succ']

lemma dq_iterK_succ (f : S × A → ℝ) (j : ℕ) (p : S × A) :
    (dqK M π)^[j + 1] f p = (M.P p.2 *ᵥ (Ppol M π ^ j *ᵥ dqPi π f)) p.1 := by
  rw [Function.iterate_succ_apply', dqK, ← dq_Pi_iterK M π f j]
  rfl


end Paths

section Eq5

variable {S : Type} [Fintype S] [DecidableEq S] (M : MDP S (Fin 2))

/-- Sign weight of the DQ estimator. -/
noncomputable def dqg (p : S × Fin 2) : ℝ :=
  2 * ((if p.2 = 1 then 1 else 0) - (if p.2 = 0 then 1 else 0))

/-- Reward as a state-action function. -/
noncomputable def dqf (p : S × Fin 2) : ℝ := M.r p.1 p.2

/-- `w_j(s)`: `j = 0` gives `r(s,1)-r(s,0)`, `j+1` gives `((P₁-P₀) P^j r_{1/2})(s)`. -/
noncomputable def dqW (j : ℕ) (s : S) : ℝ :=
  dqPi piHalf (fun p => dqg p * (dqK M piHalf)^[j] (dqf M) p) s

/-- `c(t,j) = ρᵀ P^t w_j`. -/
noncomputable def dqc (t j : ℕ) : ℝ := ∑ s, M.ρ s * (Ppol M piHalf ^ t *ᵥ dqW M j) s

lemma dq_W_eq (j : ℕ) (s : S) :
    dqW M j s = (dqK M piHalf)^[j] (dqf M) (s, 1) - (dqK M piHalf)^[j] (dqf M) (s, 0) := by
  simp [dqW, dqPi, piHalf, Fin.sum_univ_two, dqg]
  ring

lemma dq_W_zero (s : S) : dqW M 0 s = M.r s 1 - M.r s 0 := by
  rw [dq_W_eq]; rfl

lemma dq_W_succ (j : ℕ) (s : S) :
    dqW M (j + 1) s = (M.P 1 *ᵥ (Ppol M piHalf ^ j *ᵥ rpol M piHalf)) s -
      (M.P 0 *ᵥ (Ppol M piHalf ^ j *ᵥ rpol M piHalf)) s := by
  rw [dq_W_eq, dq_iterK_succ, dq_iterK_succ]
  rfl

lemma dq_policy_half : IsPolicy (piHalf : S → Fin 2 → ℝ) := by
  refine ⟨fun _ _ => by simp [piHalf], fun _ => ?_⟩
  simp [piHalf, Fin.sum_univ_two]

lemma dq_policy_one : IsPolicy (pi1 : S → Fin 2 → ℝ) := by
  refine ⟨fun _ _ => by simp only [pi1]; split_ifs <;> norm_num, fun _ => ?_⟩
  simp [pi1, Fin.sum_univ_two]

lemma dq_policy_zero : IsPolicy (pi0 : S → Fin 2 → ℝ) := by
  refine ⟨fun _ _ => by simp only [pi0]; split_ifs <;> norm_num, fun _ => ?_⟩
  simp [pi0, Fin.sum_univ_two]

lemma dq_expDQ_terms (hM : M.Standing) (H : ℕ) :
    expDQTrunc M H = ∑ t : Fin (H + 1),
      ∑ t' ∈ Finset.univ.filter (fun t' : Fin (H + 1) => t ≤ t'),
        dqc M t.val (t'.val - t.val) := by
  have e1 : dqTrunc M H = fun ω => ∑ t : Fin (H + 1),
      ∑ t' ∈ Finset.univ.filter (fun t' : Fin (H + 1) => t ≤ t'),
        dqg (ω t) * dqf M (ω t') := by
    funext ω
    simp only [dqTrunc, Finset.mul_sum]
    rfl
  unfold expDQTrunc
  rw [e1, dq_pathExp_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dq_pathExp_sum]
  refine Finset.sum_congr rfl fun t' ht' => ?_
  have hle : t.val ≤ t'.val := by
    simp only [Finset.mem_filter] at ht'
    exact ht'.2
  have := dq_pathExp_pair M piHalf hM dq_policy_half dqg (dqf M) H t.val t'.val t.isLt t'.isLt hle
  exact this

lemma dq_reindex (φ : ℕ → ℕ → ℝ) (H : ℕ) :
    ∑ t : Fin (H + 1), ∑ t' ∈ Finset.univ.filter (fun t' : Fin (H + 1) => t ≤ t'),
        φ t.val (t'.val - t.val) =
      ∑ n ∈ Finset.range (H + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, φ p.1 p.2 := by
  have inner : ∀ t : Fin (H + 1),
      ∑ t' ∈ Finset.univ.filter (fun t' : Fin (H + 1) => t ≤ t'), φ t.val (t'.val - t.val) =
        ∑ m ∈ Finset.Ico t.val (H + 1), φ t.val (m - t.val) := by
    intro t
    rw [Finset.sum_filter]
    trans ∑ a : Fin (H + 1), (fun m => if t.val ≤ m then φ t.val (m - t.val) else 0) a.val
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Fin.le_iff_val_le_val]
    rw [Fin.sum_univ_eq_sum_range (fun m => if t.val ≤ m then φ t.val (m - t.val) else 0)]
    rw [← Finset.sum_filter, Finset.range_eq_Ico, Finset.Ico_filter_le, max_eq_right (Nat.zero_le _)]
  simp only [inner]
  rw [Fin.sum_univ_eq_sum_range (fun t => ∑ m ∈ Finset.Ico t (H + 1), φ t (m - t)),
    Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => φ i j), Finset.range_eq_Ico]

lemma dq_tendsto_antidiag (φ : ℕ → ℕ → ℝ) (L : ℝ) (h : HasSum (fun p : ℕ × ℕ => φ p.1 p.2) L) :
    Filter.Tendsto (fun H => ∑ n ∈ Finset.range (H + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, φ p.1 p.2)
      Filter.atTop (nhds L) := by
  have h1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr h
  have h2 : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, φ p.1 p.2) L := by
    refine h1.sigma fun n => ?_
    rw [← Finset.sum_coe_sort]
    exact hasSum_fintype _
  exact h2.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)


variable (hM : M.Standing) (Sabs : Set S) [DecidablePred (· ∈ Sabs)]

include hM

lemma dq_Pa_closed (habs : IsAbsorbingFor M Sabs piHalf) (a : Fin 2) :
    ∀ s ∈ Sabs, ∀ s' ∉ Sabs, M.P a s s' = 0 := by
  intro s hs s' hs'
  have h := habs.1 s hs s' hs'
  simp only [Ppol, piHalf, Fin.sum_univ_two] at h
  have h0 := hM.1 0 s s'
  have h1 := hM.1 1 s s'
  fin_cases a
  · show M.P 0 s s' = 0; linarith
  · show M.P 1 s s' = 0; linarith

lemma dq_P_le_one (a : Fin 2) (s s' : S) : M.P a s s' ≤ 1 := by
  have := hM.2.1 a s
  rw [← this]
  exact Finset.single_le_sum (f := fun u => M.P a s u) (fun u _ => hM.1 a s u) (Finset.mem_univ s')

omit hM in
lemma dq_r_le (s : S) (a : Fin 2) : |M.r s a| ≤ ∑ s, ∑ a, |M.r s a| := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun s => ∑ a, |M.r s a|)
    (fun s _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s))
  exact Finset.single_le_sum (f := fun a => |M.r s a|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ a)

omit hM in
lemma dq_rpol_le (s : S) : |rpol M piHalf s| ≤ ∑ s, ∑ a, |M.r s a| := by
  have h0 := dq_r_le M s 0
  have h1 := dq_r_le M s 1
  have e : rpol M piHalf s = 1 / 2 * M.r s 0 + 1 / 2 * M.r s 1 := by
    simp [rpol, piHalf, Fin.sum_univ_two]
  rw [e]
  calc |1 / 2 * M.r s 0 + 1 / 2 * M.r s 1| ≤ |1 / 2 * M.r s 0| + |1 / 2 * M.r s 1| :=
        abs_add_le _ _
    _ = 1 / 2 * |M.r s 0| + 1 / 2 * |M.r s 1| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    _ ≤ _ := by linarith

lemma dq_W_V0 (habs : IsAbsorbingFor M Sabs piHalf) (j : ℕ) :
    ∀ s ∈ Sabs, dqW M j s = 0 := by
  have hr : ∀ s ∈ Sabs, rpol M piHalf s = 0 := fun s hs => by simp [rpol, habs.2 s hs]
  have hv := dq_mulVec_V0 Sabs _ (dq_pow_closed Sabs _ habs.1 j) _ hr
  intro s hs
  cases j with
  | zero => rw [dq_W_zero, habs.2 s hs, habs.2 s hs, sub_zero]
  | succ j =>
    have hv := dq_mulVec_V0 Sabs _ (dq_pow_closed Sabs _ habs.1 j) _ hr
    rw [dq_W_succ, dq_mulVec_V0 Sabs _ (dq_Pa_closed M hM Sabs habs 1) _ hv s hs,
      dq_mulVec_V0 Sabs _ (dq_Pa_closed M hM Sabs habs 0) _ hv s hs, sub_zero]

/-- the bound sequence `β_j` -/
noncomputable def dqβ (j : ℕ) : ℝ :=
  if j = 0 then 2 * ∑ s, ∑ a, |M.r s a|
  else (∑ s, ∑ a, |M.r s a|) * ∑ s', dqm M piHalf Sabs (j - 1) s'

omit hM in
lemma dq_m_nonneg (hM : M.Standing) (t : ℕ) (s : S) : 0 ≤ dqm M piHalf Sabs t s :=
  Finset.sum_nonneg fun s' _ => by
    split_ifs
    · exact le_refl 0
    · exact dq_pow_nonneg _ (dq_ppol_nonneg M hM piHalf dq_policy_half.1) t s s'

lemma dq_W_bound (habs : IsAbsorbingFor M Sabs piHalf) (j : ℕ) (s : S) :
    |dqW M j s| ≤ dqβ M Sabs j := by
  have hr : ∀ s ∈ Sabs, rpol M piHalf s = 0 := fun s hs => by simp [rpol, habs.2 s hs]
  cases j with
  | zero =>
    rw [dq_W_zero]
    simp only [dqβ, if_true]
    have h0 := dq_r_le M s 0
    have h1 := dq_r_le M s 1
    calc |M.r s 1 - M.r s 0| ≤ |M.r s 1| + |M.r s 0| := abs_sub _ _
      _ ≤ _ := by linarith
  | succ j =>
    rw [dq_W_succ]
    simp only [dqβ, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have hvb : ∀ s', |(Ppol M piHalf ^ j *ᵥ rpol M piHalf) s'| ≤
        (∑ s, ∑ a, |M.r s a|) * dqm M piHalf Sabs j s' := fun s' =>
      dq_mulVec_bound Sabs _ (dq_pow_nonneg _ (dq_ppol_nonneg M hM piHalf dq_policy_half.1) j)
        _ hr _ (dq_rpol_le M) s'
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← sub_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s' _ => ?_
    rw [abs_mul]
    have hp : |M.P 1 s s' - M.P 0 s s'| ≤ 1 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [dq_P_le_one M hM 0 s s', dq_P_le_one M hM 1 s s',
        hM.1 0 s s', hM.1 1 s s']
    calc |M.P 1 s s' - M.P 0 s s'| * |(Ppol M piHalf ^ j *ᵥ rpol M piHalf) s'|
        ≤ 1 * ((∑ s, ∑ a, |M.r s a|) * dqm M piHalf Sabs j s') :=
          mul_le_mul hp (hvb s') (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

lemma dq_c_summable (T : ℝ) (habs : IsAbsorbingFor M Sabs piHalf)
    (ht : AbsTimeLT M Sabs piHalf T) :
    Summable (fun p : ℕ × ℕ => dqc M p.1 p.2) := by
  have hm : ∀ s, Summable (fun t => dqm M piHalf Sabs t s) := fun s => by
    obtain ⟨x, hx, -⟩ := ht s
    exact hx.summable
  have hR0 : 0 ≤ ∑ s, ∑ a, |M.r s a| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hα : Summable (fun t => ∑ s, M.ρ s * dqm M piHalf Sabs t s) :=
    summable_sum fun s _ => (hm s).mul_left _
  have hμ : Summable (fun j => ∑ s', dqm M piHalf Sabs j s') := summable_sum fun s _ => hm s
  have hβ : Summable (dqβ M Sabs) := by
    rw [← summable_nat_add_iff 1]
    have := hμ.mul_left (∑ s, ∑ a, |M.r s a|)
    simpa [dqβ] using this
  have hα0 : 0 ≤ (fun t => ∑ s, M.ρ s * dqm M piHalf Sabs t s) := fun t =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hM.2.2.1 s) (dq_m_nonneg M Sabs hM t s)
  have hβ0 : 0 ≤ dqβ M Sabs := fun j => by
    show (0 : ℝ) ≤ dqβ M Sabs j
    unfold dqβ
    split_ifs
    · linarith
    · exact mul_nonneg hR0 (Finset.sum_nonneg fun s _ => dq_m_nonneg M Sabs hM _ s)
  refine Summable.of_norm_bounded (Summable.mul_of_nonneg hα hβ hα0 hβ0) fun p => ?_
  rw [Real.norm_eq_abs]
  unfold dqc
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [abs_mul, abs_of_nonneg (hM.2.2.1 s), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hM.2.2.1 s)
  rw [mul_comm]
  exact dq_mulVec_bound Sabs _ (dq_pow_nonneg _ (dq_ppol_nonneg M hM piHalf
    dq_policy_half.1) p.1) _ (dq_W_V0 M hM Sabs habs p.2) _ (dq_W_bound M hM Sabs habs p.2) s

lemma dq_Qsa_eq (T : ℝ) (habs : IsAbsorbingFor M Sabs piHalf)
    (ht : AbsTimeLT M Sabs piHalf T) (a : Fin 2) (s : S) :
    Qsa M piHalf s a = M.r s a + (M.P a *ᵥ dqN M piHalf (rpol M piHalf)) s := by
  have hr : ∀ s ∈ Sabs, rpol M piHalf s = 0 := fun s hs => by simp [rpol, habs.2 s hs]
  unfold Qsa
  rw [(dq_tsum_mulVec M hM Sabs piHalf dq_policy_half.1 T ht _ hr (M.P a) s).tsum_eq]

lemma dq_W_hasSum (T : ℝ) (habs : IsAbsorbingFor M Sabs piHalf)
    (ht : AbsTimeLT M Sabs piHalf T) (u : S) :
    HasSum (fun j => dqW M j u) (Qsa M piHalf u 1 - Qsa M piHalf u 0) := by
  have hr : ∀ s ∈ Sabs, rpol M piHalf s = 0 := fun s hs => by simp [rpol, habs.2 s hs]
  apply (hasSum_nat_add_iff' 1).mp
  have h1 := dq_tsum_mulVec M hM Sabs piHalf dq_policy_half.1 T ht _ hr (M.P 1) u
  have h0 := dq_tsum_mulVec M hM Sabs piHalf dq_policy_half.1 T ht _ hr (M.P 0) u
  convert h1.sub h0 using 1
  · funext j
    rw [dq_W_succ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · rw [dq_Qsa_eq M hM Sabs T habs ht, dq_Qsa_eq M hM Sabs T habs ht]
    simp [dq_W_zero]
    ring

theorem dq_eq_5 (T : ℝ) (habs : IsAbsorbingFor M Sabs piHalf)
    (ht : AbsTimeLT M Sabs piHalf T) :
    ∃ L : ℝ,
      Filter.Tendsto (fun H => expDQTrunc M H) Filter.atTop (nhds L) ∧
      HasSum (fun t : ℕ => pathExp M piHalf t
        (fun ω => Qsa M piHalf (ω (Fin.last t)).1 1 -
          Qsa M piHalf (ω (Fin.last t)).1 0)) L := by
  have hc := dq_c_summable M hM Sabs T habs ht
  refine ⟨∑' p : ℕ × ℕ, dqc M p.1 p.2, ?_, ?_⟩
  · have e : (fun H => expDQTrunc M H) = fun H => ∑ n ∈ Finset.range (H + 1),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, dqc M p.1 p.2 := by
      funext H
      rw [dq_expDQ_terms M hM H, dq_reindex]
    rw [e]
    exact dq_tendsto_antidiag (dqc M) _ hc.hasSum
  · have e : (fun t : ℕ => pathExp M piHalf t
        (fun ω => Qsa M piHalf (ω (Fin.last t)).1 1 - Qsa M piHalf (ω (Fin.last t)).1 0)) =
        fun t => ∑ s, M.ρ s * (Ppol M piHalf ^ t *ᵥ
          (fun u => Qsa M piHalf u 1 - Qsa M piHalf u 0)) s := by
      funext t
      have hpi : dqPi piHalf (fun p : S × Fin 2 => Qsa M piHalf p.1 1 - Qsa M piHalf p.1 0) =
          fun u => Qsa M piHalf u 1 - Qsa M piHalf u 0 := by
        funext u
        simp [dqPi, piHalf, Fin.sum_univ_two]
      rw [dq_pathExp_last M piHalf t (fun p => Qsa M piHalf p.1 1 - Qsa M piHalf p.1 0), hpi]
    rw [e]
    refine hc.hasSum.prod_fiberwise fun t => ?_
    unfold dqc
    simp only [Matrix.mulVec, dotProduct]
    exact hasSum_sum fun s _ => (hasSum_sum fun u _ =>
      (dq_W_hasSum M hM Sabs T habs ht u).mul_left _).mul_left _


omit hM in
lemma dq_ppol_one : Ppol M (pi1 : S → Fin 2 → ℝ) = M.P 1 := by
  ext s s'
  simp [Ppol, pi1, Fin.sum_univ_two]

omit hM in
lemma dq_ppol_zero : Ppol M (pi0 : S → Fin 2 → ℝ) = M.P 0 := by
  ext s s'
  simp [Ppol, pi0, Fin.sum_univ_two]

omit hM in
lemma dq_ppol_half : Ppol M (piHalf : S → Fin 2 → ℝ) = (1 / 2 : ℝ) • M.P 0 + (1 / 2 : ℝ) • M.P 1 := by
  ext s s'
  simp [Ppol, piHalf, Fin.sum_univ_two]

omit hM in
lemma dq_rpol_half : rpol M (piHalf : S → Fin 2 → ℝ) =
    (1 / 2 : ℝ) • rpol M pi0 + (1 / 2 : ℝ) • rpol M pi1 := by
  funext s
  simp [rpol, piHalf, pi0, pi1, Fin.sum_univ_two]

theorem dq_k1_identity (T : ℝ) (hA1 : Assumption1 M Sabs T) :
    Filter.Tendsto (fun H => expDQTrunc M H) Filter.atTop
      (nhds (Etilde M piHalf (fun s =>
          DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s) -
        Etilde M piHalf (fun s =>
          DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s))) := by
  obtain ⟨⟨habs0, ht0⟩, ⟨habs1, ht1⟩, ⟨habsH, htH⟩⟩ := hA1
  have hπH := (dq_policy_half : IsPolicy (piHalf : S → Fin 2 → ℝ))
  have hπ1 := (dq_policy_one : IsPolicy (pi1 : S → Fin 2 → ℝ))
  have hπ0 := (dq_policy_zero : IsPolicy (pi0 : S → Fin 2 → ℝ))
  obtain ⟨L, hT, hS⟩ := dq_eq_5 M hM Sabs T habsH htH
  -- the Q-difference
  set q : S → ℝ := fun u => Qsa M piHalf u 1 - Qsa M piHalf u 0 with hq
  have hS' : HasSum (fun t : ℕ => ∑ s, M.ρ s * (Ppol M piHalf ^ t *ᵥ q) s) L := by
    convert hS using 2 with t
    have hpi : dqPi piHalf (fun p : S × Fin 2 => Qsa M piHalf p.1 1 - Qsa M piHalf p.1 0) =
        q := by
      funext u
      simp [hq, dqPi, piHalf, Fin.sum_univ_two]
    rw [dq_pathExp_last M piHalf t (fun p => Qsa M piHalf p.1 1 - Qsa M piHalf p.1 0), hpi]
  have hLq : L = Etilde M piHalf q := hS'.tsum_eq.symm
  -- vanishing on the absorbing class
  have V1 := dq_DQ_V0 M hM Sabs piHalf pi1 hπH hπ1 T habsH htH habs1
  have V0' := dq_DQ_V0 M hM Sabs piHalf pi0 hπH hπ0 T habsH htH habs0
  have hX : ∀ s ∈ Sabs, (fun s => DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s) s = 0 :=
    fun s hs => by simp [V1 0 s hs, V1 1 s hs]
  have hY : ∀ s ∈ Sabs, (fun s => DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s) s = 0 :=
    fun s hs => by simp [V0' 0 s hs, V0' 1 s hs]
  rw [dq_Etilde_sub M hM Sabs piHalf hπH.1 T htH _ _ hX hY]
  convert hT using 2
  rw [hLq]
  congr 1
  -- pointwise identity
  have hr0 : ∀ s ∈ Sabs, rpol M pi0 s = 0 := fun s hs => by simp [rpol, habs0.2 s hs]
  have hr1 : ∀ s ∈ Sabs, rpol M pi1 s = 0 := fun s hs => by simp [rpol, habs1.2 s hs]
  have hNh : dqN M piHalf (rpol M piHalf) =
      (1 / 2 : ℝ) • dqN M piHalf (rpol M pi0) + (1 / 2 : ℝ) • dqN M piHalf (rpol M pi1) := by
    funext u
    have hs0 : ∀ s ∈ Sabs, ((1 / 2 : ℝ) • rpol M pi0) s = 0 := fun s hs => by simp [hr0 s hs]
    have hs1 : ∀ s ∈ Sabs, ((1 / 2 : ℝ) • rpol M pi1) s = 0 := fun s hs => by simp [hr1 s hs]
    rw [dq_rpol_half, dq_N_add M hM Sabs piHalf hπH.1 T htH _ _ hs0 hs1 u]
    simp only [dq_N_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext s
  simp only [Pi.sub_apply]
  rw [dq_DQ_succ M hM Sabs piHalf pi1 hπH hπ1 T htH 0 (V1 0) s,
    dq_DQ_succ M hM Sabs piHalf pi0 hπH hπ0 T htH 0 (V0' 0) s]
  rw [show DQ M piHalf pi1 0 = rpol M pi1 from rfl, show DQ M piHalf pi0 0 = rpol M pi0 from rfl]
  simp only [hq, dq_Qsa_eq M hM Sabs T habsH htH, hNh, dq_ppol_one, dq_ppol_zero,
    dq_ppol_half]
  show (rpol M pi1 s + _) - (rpol M pi0 s + _) = _
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [rpol, pi1, pi0, Fin.sum_univ_two]
  simp
  ring

end Eq5

end DouyinDQ.Bias

open DouyinDQ.Bias

theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S (Fin 2)) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (Tabs δ : ℝ)
    (hA1 : Assumption1 M Sabs Tabs)
    (hδ : ∀ s, ∑ s', |M.P 1 s s' - M.P 0 s s'| ≤ δ) :
    ∃ L : ℝ,
      Filter.Tendsto (fun H => expDQTrunc M H) Filter.atTop (nhds L) ∧
      |ATE M - L| ≤ Tabs ^ 3 * rmax M * δ ^ 2 := by
  have hk1 := DouyinDQ.Bias.k1_identity M hM Sabs Tabs hA1
  obtain ⟨⟨habs0, ht0⟩, ⟨habs1, ht1⟩, ⟨habsH, htH⟩⟩ := hA1
  have hπH := (dq_policy_half : IsPolicy (piHalf : S → Fin 2 → ℝ))
  have hπ1 := (dq_policy_one : IsPolicy (pi1 : S → Fin 2 → ℝ))
  have hπ0 := (dq_policy_zero : IsPolicy (pi0 : S → Fin 2 → ℝ))
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hM.2.2.2
    simp at this
  refine ⟨_, hk1, ?_⟩
  -- the estimands are the value functionals
  have hJ1 : totalReward M pi1 = Etilde M pi1 (rpol M pi1) :=
    (DouyinDQ.Bias.path_value M hM Sabs Tabs pi1 hπ1 habs1 ht1).tsum_eq
  have hJ0 : totalReward M pi0 = Etilde M pi0 (rpol M pi0) :=
    (DouyinDQ.Bias.path_value M hM Sabs Tabs pi0 hπ0 habs0 ht0).tsum_eq
  -- the transition distance between the experiment and each global policy
  have hδ1 : ∀ s, ∑ s', |Ppol M piHalf s s' - Ppol M pi1 s s'| ≤ δ / 2 := by
    intro s
    rw [dq_ppol_half, dq_ppol_one]
    have : ∀ s', |((1 / 2 : ℝ) • M.P 0 + (1 / 2 : ℝ) • M.P 1) s s' - M.P 1 s s'| =
        |M.P 1 s s' - M.P 0 s s'| / 2 := by
      intro s'
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show 1 / 2 * M.P 0 s s' + 1 / 2 * M.P 1 s s' - M.P 1 s s' =
        -(M.P 1 s s' - M.P 0 s s') / 2 by ring, abs_div, abs_neg]
      norm_num
    simp only [this, ← Finset.sum_div]
    linarith [hδ s]
  have hδ0 : ∀ s, ∑ s', |Ppol M piHalf s s' - Ppol M pi0 s s'| ≤ δ / 2 := by
    intro s
    rw [dq_ppol_half, dq_ppol_zero]
    have : ∀ s', |((1 / 2 : ℝ) • M.P 0 + (1 / 2 : ℝ) • M.P 1) s s' - M.P 0 s s'| =
        |M.P 1 s s' - M.P 0 s s'| / 2 := by
      intro s'
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show 1 / 2 * M.P 0 s s' + 1 / 2 * M.P 1 s s' - M.P 0 s s' =
        (M.P 1 s s' - M.P 0 s s') / 2 by ring, abs_div]
      norm_num
    simp only [this, ← Finset.sum_div]
    linarith [hδ s]
  have c1 := DouyinDQ.Bias.corollary_1 M hM Sabs Tabs (δ / 2) piHalf pi1 hπH hπ1
    habsH htH habs1 ht1 hδ1 1
  have c0 := DouyinDQ.Bias.corollary_1 M hM Sabs Tabs (δ / 2) piHalf pi0 hπH hπ0
    habsH htH habs0 ht0 hδ0 1
  -- the first-order sums are the functionals of DQ⁰ + DQ¹
  have V1 := dq_DQ_V0 M hM Sabs piHalf pi1 hπH hπ1 Tabs habsH htH habs1
  have V0' := dq_DQ_V0 M hM Sabs piHalf pi0 hπH hπ0 Tabs habsH htH habs0
  have s1 : ∑ k ∈ Finset.range (1 + 1), Etilde M piHalf (DQ M piHalf pi1 k) =
      Etilde M piHalf (fun s => DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    exact dq_Etilde_add M hM Sabs piHalf hπH.1 Tabs htH _ _ (V1 0) (V1 1)
  have s0 : ∑ k ∈ Finset.range (1 + 1), Etilde M piHalf (DQ M piHalf pi0 k) =
      Etilde M piHalf (fun s => DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    exact dq_Etilde_add M hM Sabs piHalf hπH.1 Tabs htH _ _ (V0' 0) (V0' 1)
  rw [s1] at c1
  rw [s0] at c0
  -- reward scales
  have hbdd : ∀ s, BddAbove (Set.range fun a => |M.r s a|) := fun s =>
    (Set.finite_range _).bddAbove
  have hbdd' : BddAbove (Set.range fun s => ⨆ a, |M.r s a|) := (Set.finite_range _).bddAbove
  have hra : ∀ s a, |M.r s a| ≤ rmax M := fun s a =>
    (le_ciSup (hbdd s) a).trans (le_ciSup hbdd' s)
  have hR1 : (⨆ s, |rpol M pi1 s|) ≤ rmax M := by
    refine ciSup_le fun s => ?_
    have : rpol M pi1 s = M.r s 1 := by simp [rpol, pi1, Fin.sum_univ_two]
    rw [this]; exact hra s 1
  have hR0 : (⨆ s, |rpol M pi0 s|) ≤ rmax M := by
    refine ciSup_le fun s => ?_
    have : rpol M pi0 s = M.r s 0 := by simp [rpol, pi0, Fin.sum_univ_two]
    rw [this]; exact hra s 0
  have hT : 0 ≤ Tabs := dq_T_nonneg M hM Sabs piHalf Tabs htH hπH.1
  have hrm : 0 ≤ rmax M := (abs_nonneg _).trans (hra (Classical.arbitrary S) 0)
  have hK : 0 ≤ (δ / 2 * Tabs) ^ (1 + 1) * Tabs := mul_nonneg (sq_nonneg _) hT
  have e1 := c1.trans (mul_le_mul_of_nonneg_left hR1 hK)
  have e0 := c0.trans (mul_le_mul_of_nonneg_left hR0 hK)
  unfold ATE
  rw [hJ1, hJ0]
  have tri : |Etilde M pi1 (rpol M pi1) - Etilde M pi0 (rpol M pi0) -
      (Etilde M piHalf (fun s => DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s) -
        Etilde M piHalf (fun s => DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s))| ≤
      |Etilde M pi1 (rpol M pi1) -
        Etilde M piHalf (fun s => DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s)| +
      |Etilde M pi0 (rpol M pi0) -
        Etilde M piHalf (fun s => DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s)| := by
    rw [show Etilde M pi1 (rpol M pi1) - Etilde M pi0 (rpol M pi0) -
      (Etilde M piHalf (fun s => DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s) -
        Etilde M piHalf (fun s => DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s)) =
      (Etilde M pi1 (rpol M pi1) -
        Etilde M piHalf (fun s => DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s)) -
      (Etilde M pi0 (rpol M pi0) -
        Etilde M piHalf (fun s => DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s)) by ring]
    exact abs_sub _ _
  refine tri.trans ((add_le_add e1 e0).trans ?_)
  have : (δ / 2 * Tabs) ^ (1 + 1) * Tabs * rmax M + (δ / 2 * Tabs) ^ (1 + 1) * Tabs * rmax M =
      (Tabs ^ 3 * rmax M * δ ^ 2) / 2 := by ring
  rw [this]
  have : 0 ≤ Tabs ^ 3 * rmax M * δ ^ 2 :=
    mul_nonneg (mul_nonneg (pow_nonneg hT 3) hrm) (sq_nonneg δ)
  linarith
