-- Prove2me | solution 1 for DouyinDQ.Bias.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:33:47.037468+00:00
-- url     : https://prove2.me/submissions/98f1e6a0-dbef-4d57-bfdb-4fc6341ee94f

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

end DouyinDQ.Bias

open DouyinDQ.Bias

theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A]
    (M : MDP S A) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (Tabs δ : ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (habsπ : IsAbsorbingFor M Sabs π) (htπ : AbsTimeLT M Sabs π Tabs)
    (habsπ' : IsAbsorbingFor M Sabs π') (htπ' : AbsTimeLT M Sabs π' Tabs)
    (hδ : ∀ s, ∑ s', |Ppol M π s s' - Ppol M π' s s'| ≤ δ)
    (K : ℕ) :
    |Etilde M π' (rpol M π') -
      ∑ k ∈ Finset.range (K + 1), Etilde M π (DQ M π π' k)| ≤
      (δ * Tabs) ^ (K + 1) * Tabs * (⨆ s, |rpol M π' s|) :=
  dq_corollary_1 M hM Sabs π π' hπ hπ' Tabs δ habsπ htπ habsπ' htπ' hδ K _
    (fun s => le_ciSup (f := fun s => |rpol M π' s|) (Set.finite_range _).bddAbove s)
