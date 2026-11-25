-- Prove2me | solution 1 for FracTruthSched.padding_sequence_limit
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T19:22:46.969009+00:00
-- url     : https://prove2.me/submissions/d9676431-4cca-4ceb-ba72-78e67c9f2f2a

import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric
import Definitions.Def_FracTruthSched_PaddingSequence

/-
PLAN (two ultrafilter limits along `U = hyperfilter ℕ`, so `U ≤ atTop`).
* Generic `limMech U N`: pointwise `limUnder U` of allocations and payments.  Bounded sequences
  converge along an ultrafilter (compactness of `Icc`).  Generic transfer lemmas: feasibility,
  truthfulness (with vanishing error), linear upper bounds (with vanishing error),
  disutility symmetry.                                                        (~150 lines)
* Stage 1: `Mr = limMech U M'` where `M'_K` is `S.M K` with normalised payments
  `P_K(t) - P_K(t with row i zeroed)` (in `[-Σ t_i, 0]` by truthfulness).  Inherits everything
  at all graph inputs, and unique zeros / zero-type irrelevance at rational graph inputs.
                                                                              (~120 lines)
* Stage 2: `M = limMech U N`, `N_h(t) = Mr(R_h t)`, `R_h a = ⌈(h+1)a⌉/(h+1)` entrywise, which maps
  graph inputs to rational graph inputs, commutes with row updates and relabellings, and fixes 0.
  Truthfulness error `Σ_e (R_h t_ie - t_ie) → 0`; load error via continuity of `C`.  (~150 lines)
-/

set_option autoImplicit false

open Filter Topology

namespace FracTruthSchedPSL

open FracTruthSched

variable {n : ℕ} {τ : Type*}

/-! ### Generic ultrafilter limits -/

theorem tendsto_limU (U : Ultrafilter ℕ) (f : ℕ → ℝ) (a b : ℝ) (h : ∀ k, f k ∈ Set.Icc a b) :
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) ∧
      limUnder (U : Filter ℕ) f ∈ Set.Icc a b := by
  have hc : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨x, hx, hle⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact Filter.mem_map.2 (Filter.Eventually.of_forall h))
  have ht : Tendsto f (U : Filter ℕ) (𝓝 x) := hle
  have h2 := tendsto_nhds_limUnder ⟨x, ht⟩
  refine ⟨h2, ?_⟩
  rw [tendsto_nhds_unique h2 ht]; exact hx

theorem tendsto_limU' (U : Ultrafilter ℕ) (f : ℕ → ℝ) (B : ℝ) (h : ∀ k, |f k| ≤ B) :
    Tendsto f (U : Filter ℕ) (𝓝 (limUnder (U : Filter ℕ) f)) :=
  (tendsto_limU U f (-B) B (fun k => abs_le.mp (h k))).1

/-- The pointwise ultrafilter limit of a sequence of mechanisms. -/
noncomputable def limMech (U : Ultrafilter ℕ) (N : ℕ → FracMech n τ) : FracMech n τ where
  x t i e := limUnder (U : Filter ℕ) (fun k => (N k).x t i e)
  P t i := limUnder (U : Filter ℕ) (fun k => (N k).P t i)

section generic

variable (U : Ultrafilter ℕ) {N : ℕ → FracMech n τ} {D : (Fin n → τ → ℝ) → Prop}

theorem lim_x_tendsto (hF : ∀ k, IsFeasibleOn D (N k)) {t : Fin n → τ → ℝ} (ht : D t)
    (i : Fin n) (e : τ) :
    Tendsto (fun k => (N k).x t i e) (U : Filter ℕ) (𝓝 ((limMech U N).x t i e)) :=
  (tendsto_limU U _ 0 1 (fun k => (hF k t ht).1 i e)).1

theorem lim_P_tendsto (hP : ∀ t, D t → ∀ i, ∃ a b : ℝ, ∀ k, (N k).P t i ∈ Set.Icc a b)
    {t : Fin n → τ → ℝ} (ht : D t) (i : Fin n) :
    Tendsto (fun k => (N k).P t i) (U : Filter ℕ) (𝓝 ((limMech U N).P t i)) := by
  obtain ⟨a, b, h⟩ := hP t ht i
  exact (tendsto_limU U _ a b h).1

theorem lim_P_mem {t : Fin n → τ → ℝ} {i : Fin n} {a b : ℝ} (h : ∀ k, (N k).P t i ∈ Set.Icc a b) :
    (limMech U N).P t i ∈ Set.Icc a b :=
  (tendsto_limU U _ a b h).2

theorem limMech_feasible (hF : ∀ k, IsFeasibleOn D (N k)) : IsFeasibleOn D (limMech U N) := by
  intro t ht
  refine ⟨fun i j => (tendsto_limU U _ 0 1 (fun k => (hF k t ht).1 i j)).2, fun j => ?_⟩
  have h1 : Tendsto (fun k => ∑ i, (N k).x t i j) (U : Filter ℕ)
      (𝓝 (∑ i, (limMech U N).x t i j)) :=
    tendsto_finsetSum _ (fun i _ => lim_x_tendsto U hF ht i j)
  have hc : (fun k => ∑ i, (N k).x t i j) = fun _ => (1 : ℝ) :=
    funext fun k => (hF k t ht).2 j
  rw [hc] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem limMech_x_le (hF : ∀ k, IsFeasibleOn D (N k)) {t : Fin n → τ → ℝ} (ht : D t)
    (i : Fin n) (e : τ) (g : ℕ → ℝ) (c : ℝ) (hg : Tendsto g (U : Filter ℕ) (𝓝 c))
    (h : ∀ᶠ k in (U : Filter ℕ), (N k).x t i e ≤ g k) : (limMech U N).x t i e ≤ c :=
  le_of_tendsto_of_tendsto (lim_x_tendsto U hF ht i e) hg h

theorem limMech_sum_le [Fintype τ] (hF : ∀ k, IsFeasibleOn D (N k)) {t : Fin n → τ → ℝ}
    (ht : D t) (i : Fin n) (w : τ → ℝ) (g : ℕ → ℝ) (c : ℝ)
    (hg : Tendsto g (U : Filter ℕ) (𝓝 c)) (h : ∀ k, ∑ e, w e * (N k).x t i e ≤ g k) :
    ∑ e, w e * (limMech U N).x t i e ≤ c :=
  le_of_tendsto_of_tendsto'
    (tendsto_finsetSum _ fun e _ => (lim_x_tendsto U hF ht i e).const_mul (w e)) hg h

theorem limMech_x_congr {t t' : Fin n → τ → ℝ} {i i' : Fin n} {e e' : τ}
    (h : ∀ k, (N k).x t i e = (N k).x t' i' e') :
    (limMech U N).x t i e = (limMech U N).x t' i' e' := by
  show limUnder _ _ = limUnder _ _
  congr 1
  funext k
  exact h k

theorem limMech_x_const (hF : ∀ k, IsFeasibleOn D (N k)) {t : Fin n → τ → ℝ} (ht : D t)
    {i : Fin n} {e : τ} {c : ℝ} (h : ∀ k, (N k).x t i e = c) : (limMech U N).x t i e = c := by
  have h1 := lim_x_tendsto U hF ht i e
  have hc : (fun k => (N k).x t i e) = fun _ => c := funext h
  rw [hc] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem limMech_truthful [Fintype τ] (hF : ∀ k, IsFeasibleOn D (N k))
    (hP : ∀ t, D t → ∀ i, ∃ a b : ℝ, ∀ k, (N k).P t i ∈ Set.Icc a b)
    (happ : ∀ t, D t → ∀ (i : Fin n) (b : τ → ℝ), D (Function.update t i b) →
      ∃ ε : ℕ → ℝ, Tendsto ε (U : Filter ℕ) (𝓝 0) ∧ ∀ k,
        (N k).P (Function.update t i b) i - ∑ j, t i j * (N k).x (Function.update t i b) i j ≤
          (N k).P t i - ∑ j, t i j * (N k).x t i j + ε k) :
    IsTruthfulOn D (limMech U N) := by
  intro t ht i b hb
  obtain ⟨ε, hε, hk⟩ := happ t ht i b hb
  have T1 := (lim_P_tendsto U hP hb i).sub
    (tendsto_finsetSum Finset.univ fun j _ => (lim_x_tendsto U hF hb i j).const_mul (t i j))
  have T2 := ((lim_P_tendsto U hP ht i).sub
    (tendsto_finsetSum Finset.univ fun j _ => (lim_x_tendsto U hF ht i j).const_mul (t i j))).add hε
  have := le_of_tendsto_of_tendsto' T1 T2 hk
  simpa using this

theorem lim_disutility_tendsto [Fintype τ] (hF : ∀ k, IsFeasibleOn D (N k))
    (hP : ∀ t, D t → ∀ i, ∃ a b : ℝ, ∀ k, (N k).P t i ∈ Set.Icc a b)
    {t : Fin n → τ → ℝ} {i : Fin n} (ht : D t) (ht0 : D (Function.update t i 0)) :
    Tendsto (fun k => disutility (N k) t i) (U : Filter ℕ) (𝓝 (disutility (limMech U N) t i)) := by
  unfold disutility
  exact ((tendsto_finsetSum Finset.univ fun j _ =>
    (lim_x_tendsto U hF ht i j).const_mul (t i j)).sub (lim_P_tendsto U hP ht i)).add
      (lim_P_tendsto U hP ht0 i)

theorem limMech_disutility_congr [Fintype τ] (hF : ∀ k, IsFeasibleOn D (N k))
    (hP : ∀ t, D t → ∀ i, ∃ a b : ℝ, ∀ k, (N k).P t i ∈ Set.Icc a b)
    {t t' : Fin n → τ → ℝ} {i : Fin n} (ht : D t) (ht0 : D (Function.update t i 0))
    (ht' : D t') (ht0' : D (Function.update t' i 0))
    (h : ∀ k, disutility (N k) t i = disutility (N k) t' i) :
    disutility (limMech U N) t i = disutility (limMech U N) t' i := by
  have h1 := lim_disutility_tendsto U hF hP ht ht0
  have h2 := lim_disutility_tendsto U hF hP ht' ht0'
  rw [funext h] at h1
  exact tendsto_nhds_unique h1 h2

end generic

/-! ### Graph-input facts -/

variable {ℓ : ℕ}

theorem gi_update_zero {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (i : Fin n) :
    IsGraphInput (Function.update t i 0) := by
  intro j e
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp only [Function.update_of_ne h]; exact ht j e

theorem incident_classPerm {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ) (j : Fin n)
    (e : CoreTask n ℓ) : incident j (γ e) ↔ incident j e := by
  rcases e with ⟨p, k⟩ | k
  · obtain ⟨k', hk'⟩ := hγ.1 p k
    rw [hk']; simp [incident]
  · rw [hγ.2 k]

theorem gi_relabel {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ)
    {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) : IsGraphInput (relabel γ t) := by
  intro j e
  refine ⟨(ht j (γ e)).1, fun hn => (ht j (γ e)).2 ?_⟩
  rwa [incident_classPerm hγ]

theorem relabel_update_zero (γ : Equiv.Perm (CoreTask n ℓ)) (t : Fin n → CoreTask n ℓ → ℝ)
    (i : Fin n) : Function.update (relabel γ t) i 0 = relabel γ (Function.update t i 0) := by
  funext j e
  rcases eq_or_ne j i with rfl | h
  · simp [relabel]
  · simp [relabel, Function.update_of_ne h]

/-! ### Normalised payments -/

/-- Same allocation, payments normalised so that zeroing one's own row gives payment `0`. -/
def normM (M : FracMech n τ) : FracMech n τ :=
  ⟨M.x, fun t i => M.P t i - M.P (Function.update t i 0) i⟩

theorem normM_truthful {M : FracMech n (CoreTask n ℓ)} (h : IsTruthfulOn IsGraphInput M) :
    IsTruthfulOn IsGraphInput (normM M) := by
  intro t ht i b hb
  have := h t ht i b hb
  simp only [normM, Function.update_idem]
  linarith

theorem normM_P_mem {M : FracMech n (CoreTask n ℓ)} (hF : IsFeasibleOn IsGraphInput M)
    (h : IsTruthfulOn IsGraphInput M) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t)
    (i : Fin n) : (normM M).P t i ∈ Set.Icc (-∑ e, t i e) 0 := by
  have h0 := gi_update_zero ht i
  have h1 := h _ h0 i (t i) (by rwa [Function.update_idem, Function.update_eq_self])
  rw [Function.update_idem, Function.update_eq_self] at h1
  have h2 := h t ht i 0 h0
  simp only [Function.update_self, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at h1
  have h3 : ∑ j, t i j * M.x (Function.update t i 0) i j ≤ ∑ j, t i j :=
    Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (ht i j).1 ((hF _ h0).1 i j).2
  have h4 : 0 ≤ ∑ j, t i j * M.x t i j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (ht i j).1 ((hF _ ht).1 i j).1
  simp only [normM, Set.mem_Icc]
  constructor <;> linarith

theorem normM_disutility (M : FracMech n (CoreTask n ℓ)) (t : Fin n → CoreTask n ℓ → ℝ)
    (i : Fin n) : disutility (normM M) t i = disutility M t i := by
  simp only [disutility, normM, Function.update_idem]
  ring

/-! ### Stage 1: limit of the padded mechanisms -/

theorem hyper_le : ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ atTop :=
  Nat.cofinite_eq_atTop ▸ Filter.hyperfilter_le_cofinite

theorem tendsto_U {f : ℕ → ℝ} {c : ℝ} (h : Tendsto f atTop (𝓝 c)) :
    Tendsto f ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) (𝓝 c) :=
  h.mono_left hyper_le

theorem tendsto_add_atTop (c : ℝ) : Tendsto (fun K : ℕ => (K : ℝ) + c) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem tendsto_inv_succ : Tendsto (fun K : ℕ => 1 / ((K : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable [NeZero n] {R : (m : ℕ) → FracMech n (Fin m)} {ρ : ℝ}

/-- The stage-1 limit mechanism. -/
noncomputable def Mr (S : PaddingSequence R ρ ℓ) : FracMech n (CoreTask n ℓ) :=
  limMech (Filter.hyperfilter ℕ) (fun K => normM (S.M K))

variable (S : PaddingSequence R ρ ℓ)

theorem S_feas : ∀ K, IsFeasibleOn IsGraphInput (normM (S.M K)) := fun K => S.feasible K

theorem S_P : ∀ t, IsGraphInput t → ∀ i, ∃ a b : ℝ, ∀ K,
    (normM (S.M K)).P t i ∈ Set.Icc a b :=
  fun _ ht i => ⟨_, _, fun K => normM_P_mem (S.feasible K) (S.truthful K) ht i⟩

theorem Mr_feasible : IsFeasibleOn IsGraphInput (Mr S) := limMech_feasible _ (S_feas S)

theorem Mr_P_mem {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (i : Fin n) :
    (Mr S).P t i ∈ Set.Icc (-∑ e, t i e) 0 :=
  lim_P_mem _ fun K => normM_P_mem (S.feasible K) (S.truthful K) ht i

theorem Mr_truthful : IsTruthfulOn IsGraphInput (Mr S) := by
  refine limMech_truthful _ (S_feas S) (S_P S) fun t ht i b hb => ⟨fun _ => 0,
    tendsto_const_nhds, fun K => ?_⟩
  have := normM_truthful (S.truthful K) t ht i b hb
  linarith

theorem Mr_load (ρ' : ℝ) (hρ' : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ' * opt t) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t)
    (i : Fin n) : ∑ e, t i e * (Mr S).x t i e ≤ ρ' * C t := by
  refine limMech_sum_le _ (S_feas S) ht i (t i) (fun K => ρ' * (C t + 1 / ((K : ℝ) + 1)))
    (ρ' * C t) (tendsto_U ?_) (fun K => S.load ρ' hρ' K t ht i)
  simpa using (tendsto_inv_succ.const_add (C t)).const_mul ρ'

theorem Mr_eligible : IsEligible (Mr S) := by
  intro t ht i e hne
  have h0 := ((Mr_feasible S) t ht).1 i e
  have : (Mr S).x t i e ≤ 0 := by
    refine limMech_x_le _ (S_feas S) ht i e _ 0 (tendsto_U ?_)
      (Eventually.of_forall fun K => S.eligibility K t ht i e hne)
    have h1 : Tendsto (fun K : ℕ => ρ * (C t + 1 / ((K : ℝ) + 1))) atTop (𝓝 (ρ * (C t + 0))) :=
      (tendsto_inv_succ.const_add (C t)).const_mul ρ
    exact h1.div_atTop ((tendsto_pow_atTop two_ne_zero).comp (tendsto_add_atTop 1))
  linarith

omit [NeZero n] in
theorem edge_others {e : CoreTask n ℓ} {i j u : Fin n} (he : e.isLeft) (hi : incident i e)
    (hj : incident j e) (hij : i ≠ j) (hui : u ≠ i) (huj : u ≠ j) : ¬ incident u e := by
  rcases e with ⟨p, k⟩ | k
  · simp only [incident] at hi hj ⊢
    omega
  · simp at he

theorem Mr_uz {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsRatGraphInput t) (e : CoreTask n ℓ)
    (i j : Fin n) (he : e.isLeft) (hi : incident i e) (hj : incident j e) (hij : i ≠ j)
    (hti : t i e = 0) (htj : 0 < t j e) : (Mr S).x t i e = 1 := by
  have hF := (Mr_feasible S) t ht.1
  have hj0 : (Mr S).x t j e ≤ 0 := by
    obtain ⟨K₀, hK⟩ := S.unique_zeros t ht e i j he hi hj hij hti htj
    refine limMech_x_le _ (S_feas S) ht.1 j e _ 0 (tendsto_U ?_)
      (Filter.eventually_atTop.2 ⟨K₀, hK⟩ |>.filter_mono hyper_le)
    have h1 : Tendsto (fun K : ℕ => ρ * (C t + 1 / ((K : ℝ) + 1))) atTop (𝓝 (ρ * (C t + 0))) :=
      (tendsto_inv_succ.const_add (C t)).const_mul ρ
    exact h1.div_atTop ((tendsto_add_atTop 2).atTop_mul_const htj)
  have hsum := hF.2 e
  rw [Fintype.sum_eq_add i j hij (fun u ⟨hui, huj⟩ =>
    Mr_eligible S t ht.1 u e (edge_others he hi hj hij hui huj))] at hsum
  have := (hF.1 j e).1
  linarith

theorem Mr_zti {t t' : Fin n → CoreTask n ℓ → ℝ} (ht : IsRatGraphInput t)
    (ht' : IsRatGraphInput t') (e : CoreTask n ℓ) (he : e.isLeft)
    (hagree : ∀ u f, f ≠ e → t u f = t' u f) (hz : ∃ u, incident u e ∧ t u e = 0)
    (hz' : ∃ u, incident u e ∧ t' u e = 0) (u : Fin n) (f : CoreTask n ℓ) (hf : f ≠ e) :
    (Mr S).x t u f = (Mr S).x t' u f := by
  obtain ⟨K₀, hK⟩ := S.zero_type_irrelevance t t' ht ht' e he hagree hz hz'
  have T := ((lim_x_tendsto (Filter.hyperfilter ℕ) (S_feas S) ht.1 u f).sub
    (lim_x_tendsto (Filter.hyperfilter ℕ) (S_feas S) ht'.1 u f)).abs
  have hg : Tendsto (fun K : ℕ => 4 / ((K : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_add_atTop 2)
  have := le_of_tendsto_of_tendsto T (tendsto_U hg)
    ((Filter.eventually_atTop.2 ⟨K₀, fun K hK' => hK K hK' u f hf⟩).filter_mono hyper_le)
  have h2 := abs_nonneg ((Mr S).x t u f - (Mr S).x t' u f)
  have h3 : |(Mr S).x t u f - (Mr S).x t' u f| = 0 := le_antisymm this h2
  rw [abs_eq_zero, sub_eq_zero] at h3
  exact h3

theorem Mr_symm : IsClassSymmetric (Mr S) := by
  intro γ hγ t ht
  refine ⟨fun i e => limMech_x_congr _ fun K => ((S.symmetric K) γ hγ t ht).1 i e, fun i => ?_⟩
  have hgt := gi_relabel hγ ht
  refine limMech_disutility_congr _ (S_feas S) (S_P S) hgt (gi_update_zero hgt i) ht
    (gi_update_zero ht i) fun K => ?_
  rw [normM_disutility, normM_disutility]
  exact ((S.symmetric K) γ hγ t ht).2 i

/-! ### Stage 2: extension to real inputs by rounding up -/

/-- Rounding up to the grid `ℤ/(h+1)`. -/
noncomputable def rnd (h : ℕ) (a : ℝ) : ℝ := (⌈((h : ℝ) + 1) * a⌉ : ℝ) / ((h : ℝ) + 1)

theorem rnd_zero (h : ℕ) : rnd h 0 = 0 := by simp [rnd]

theorem rnd_ge (h : ℕ) (a : ℝ) : a ≤ rnd h a := by
  have hp : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  rw [rnd, le_div_iff₀ hp, mul_comm]
  exact Int.le_ceil _

theorem rnd_le (h : ℕ) (a : ℝ) : rnd h a ≤ a + 1 / ((h : ℝ) + 1) := by
  have hp : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  rw [rnd, div_le_iff₀ hp]
  have h1 := Int.ceil_lt_add_one (((h : ℝ) + 1) * a)
  have e : (a + 1 / ((h : ℝ) + 1)) * ((h : ℝ) + 1) = ((h : ℝ) + 1) * a + 1 := by
    field_simp
  linarith

theorem rnd_tendsto (a : ℝ) : Tendsto (fun h => rnd h a) atTop (𝓝 a) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (rnd_ge · a) (rnd_le · a)
  simpa using tendsto_inv_succ.const_add a

theorem rnd_rat (h : ℕ) (a : ℝ) : ∃ q : ℚ, rnd h a = q :=
  ⟨(⌈((h : ℝ) + 1) * a⌉ : ℚ) / ((h : ℚ) + 1), by simp [rnd]⟩

/-- Entrywise rounding of an input. -/
noncomputable def Rd (h : ℕ) (t : Fin n → CoreTask n ℓ → ℝ) : Fin n → CoreTask n ℓ → ℝ :=
  fun j e => rnd h (t j e)

omit [NeZero n] in
theorem Rd_rgi (h : ℕ) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) :
    IsRatGraphInput (Rd h t) :=
  ⟨fun j e => ⟨le_trans (ht j e).1 (rnd_ge h _), fun hn => by simp [Rd, (ht j e).2 hn, rnd_zero]⟩,
    fun j e => rnd_rat h _⟩

omit [NeZero n] in
theorem Rd_update (h : ℕ) (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n) (b : CoreTask n ℓ → ℝ) :
    Rd h (Function.update t i b) = Function.update (Rd h t) i (fun e => rnd h (b e)) := by
  funext j e
  rcases eq_or_ne j i with rfl | hj
  · simp [Rd]
  · simp [Rd, Function.update_of_ne hj]

theorem Rd_update_zero (h : ℕ) (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n) :
    Rd h (Function.update t i 0) = Function.update (Rd h t) i 0 := by
  rw [Rd_update]
  congr 1
  funext e
  exact rnd_zero h

theorem C_continuous : Continuous (fun t : Fin n → CoreTask n ℓ → ℝ => C t) := by
  unfold C
  apply Continuous.finset_inf'_apply
  intro σ _
  unfold schedMakespan
  apply Continuous.finset_sup'_apply
  intro i _
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).comp (continuous_apply i)

theorem C_Rd_tendsto (t : Fin n → CoreTask n ℓ → ℝ) :
    Tendsto (fun h => C (Rd h t)) atTop (𝓝 (C t)) :=
  (C_continuous.tendsto t).comp
    (tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun e => rnd_tendsto (t j e))

/-- The rounded stage-1 mechanisms. -/
noncomputable def Nh (h : ℕ) : FracMech n (CoreTask n ℓ) :=
  ⟨fun t => (Mr S).x (Rd h t), fun t => (Mr S).P (Rd h t)⟩

theorem Nh_feas : ∀ h, IsFeasibleOn IsGraphInput (Nh S h) :=
  fun h t ht => Mr_feasible S (Rd h t) (Rd_rgi h ht).1

theorem Nh_P : ∀ t, IsGraphInput t → ∀ i, ∃ a b : ℝ, ∀ h,
    (Nh S h).P t i ∈ Set.Icc a b := by
  intro t ht i
  refine ⟨-∑ e, (t i e + 1), 0, fun h => ?_⟩
  have hm : (Nh S h).P t i ∈ Set.Icc (-∑ e, Rd h t i e) 0 := Mr_P_mem S (Rd_rgi h ht).1 i
  have hs : ∑ e, Rd h t i e ≤ ∑ e, (t i e + 1) := by
    refine Finset.sum_le_sum fun e _ => (rnd_le h _).trans ?_
    have : 1 / ((h : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(h.cast_nonneg : (0 : ℝ) ≤ h)]
    linarith
  exact ⟨by linarith [hm.1], hm.2⟩

/-- The final mechanism. -/
noncomputable def Mfin : FracMech n (CoreTask n ℓ) := limMech (Filter.hyperfilter ℕ) (Nh S)

theorem Mfin_feasible : IsFeasibleOn IsGraphInput (Mfin S) := limMech_feasible _ (Nh_feas S)

theorem Mfin_truthful : IsTruthfulOn IsGraphInput (Mfin S) := by
  refine limMech_truthful _ (Nh_feas S) (Nh_P S) fun t ht i b hb =>
    ⟨fun h => ∑ e, (rnd h (t i e) - t i e), tendsto_U ?_, fun h => ?_⟩
  · simpa using tendsto_finsetSum Finset.univ fun e _ => (rnd_tendsto (t i e)).sub_const (t i e)
  · show (Mr S).P (Rd h (Function.update t i b)) i -
        ∑ j, t i j * (Mr S).x (Rd h (Function.update t i b)) i j ≤
      (Mr S).P (Rd h t) i - ∑ j, t i j * (Mr S).x (Rd h t) i j + ∑ e, (rnd h (t i e) - t i e)
    have hgi' := (Rd_rgi h hb).1
    rw [Rd_update] at hgi' ⊢
    have htr := Mr_truthful S (Rd h t) (Rd_rgi h ht).1 i _ hgi'
    have hF1 := Mr_feasible S _ hgi'
    have hF2 := Mr_feasible S _ (Rd_rgi h ht).1
    have h1 : ∑ j, (Rd h t i j - t i j) *
        (Mr S).x (Function.update (Rd h t) i fun e => rnd h (b e)) i j ≤
        ∑ j, (Rd h t i j - t i j) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_of_le_one_right (sub_nonneg.2 (rnd_ge h _)) (hF1.1 i j).2
    have h2 : 0 ≤ ∑ j, (Rd h t i j - t i j) * (Mr S).x (Rd h t) i j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (sub_nonneg.2 (rnd_ge h _)) (hF2.1 i j).1
    simp only [sub_mul, Finset.sum_sub_distrib] at h1 h2 ⊢
    simp only [Rd] at h1 h2 htr ⊢
    linarith

theorem Mfin_load (ρ' : ℝ) (hρ' : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ' * opt t) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t)
    (i : Fin n) : ∑ e, t i e * (Mfin S).x t i e ≤ ρ' * C t := by
  refine limMech_sum_le _ (Nh_feas S) ht i (t i) (fun h => ρ' * C (Rd h t)) (ρ' * C t)
    (tendsto_U ((C_Rd_tendsto t).const_mul ρ')) fun h => ?_
  have hgi := (Rd_rgi h ht).1
  refine le_trans ?_ (Mr_load S ρ' hρ' hgi i)
  exact Finset.sum_le_sum fun e _ =>
    mul_le_mul_of_nonneg_right (rnd_ge h _) ((Mr_feasible S _ hgi).1 i e).1

theorem Mfin_eligible : IsEligible (Mfin S) := fun t ht i e hne =>
  limMech_x_const _ (Nh_feas S) ht fun h => Mr_eligible S _ (Rd_rgi h ht).1 i e hne

theorem Mfin_uz : HasUniqueZeros (Mfin S) := by
  intro t ht e i j he hi hj hij hti htj
  refine limMech_x_const _ (Nh_feas S) ht fun h => ?_
  exact Mr_uz S (Rd_rgi h ht) e i j he hi hj hij (by simp [Rd, hti, rnd_zero])
    (lt_of_lt_of_le htj (rnd_ge h _))

theorem Mfin_zti : HasZeroTypeIrrelevance (Mfin S) := by
  intro t t' ht ht' e he hagree hz hz' u f hf
  refine limMech_x_congr _ fun h => ?_
  obtain ⟨v, hv, hv0⟩ := hz
  obtain ⟨v', hv', hv0'⟩ := hz'
  exact Mr_zti S (Rd_rgi h ht) (Rd_rgi h ht') e he
    (fun u f hf => by simp [Rd, hagree u f hf]) ⟨v, hv, by simp [Rd, hv0, rnd_zero]⟩
    ⟨v', hv', by simp [Rd, hv0', rnd_zero]⟩ u f hf

theorem Mfin_symm : IsClassSymmetric (Mfin S) := by
  intro γ hγ t ht
  have hRel : ∀ h, Rd h (relabel γ t) = relabel γ (Rd h t) := fun h => rfl
  refine ⟨fun i e => limMech_x_congr _ fun h => ?_, fun i => ?_⟩
  · show (Mr S).x (Rd h (relabel γ t)) i e = (Mr S).x (Rd h t) i (γ e)
    rw [hRel]
    exact ((Mr_symm S) γ hγ _ (Rd_rgi h ht).1).1 i e
  have hgt := gi_relabel hγ ht
  refine limMech_disutility_congr _ (Nh_feas S) (Nh_P S) hgt (gi_update_zero hgt i) ht
    (gi_update_zero ht i) fun h => ?_
  have hgi := (Rd_rgi h ht).1
  obtain ⟨hx, hd⟩ := (Mr_symm S) γ hγ _ hgi
  have hd' := hd i
  simp only [disutility] at hd' ⊢
  simp only [Nh]
  rw [hRel, Rd_update_zero, Rd_update_zero, hRel] at *
  simp only [hx] at hd' ⊢
  have e1 : ∑ e, relabel γ (Rd h t) i e * (Mr S).x (Rd h t) i (γ e) =
      ∑ e, Rd h t i e * (Mr S).x (Rd h t) i e :=
    Equiv.sum_comp γ (fun e => Rd h t i e * (Mr S).x (Rd h t) i e)
  have e2 : ∑ e, relabel γ t i e * (Mr S).x (Rd h t) i (γ e) =
      ∑ e, t i e * (Mr S).x (Rd h t) i e :=
    Equiv.sum_comp γ (fun e => t i e * (Mr S).x (Rd h t) i e)
  linarith

end FracTruthSchedPSL

open FracTruthSched in
theorem solution {n : ℕ} [NeZero n]
    (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (ρ : ℝ) (hρ : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ * opt t) (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (S : PaddingSequence R ρ ℓ) :
    ∃ M : FracMech n (CoreTask n ℓ),
      IsFeasibleOn IsGraphInput M ∧ IsTruthfulOn IsGraphInput M ∧
      (∀ t, IsGraphInput t → makespan M t ≤ ρ * C t) ∧
      (∀ ρ' : ℝ, (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
          makespan (R m) t ≤ ρ' * opt t) →
        ∀ t, IsGraphInput t → makespan M t ≤ ρ' * C t) ∧
      IsEligible M ∧ HasUniqueZeros M ∧ HasZeroTypeIrrelevance M ∧ IsClassSymmetric M := by
  have hload : ∀ ρ' : ℝ, (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ' * opt t) →
      ∀ t, IsGraphInput t → makespan (FracTruthSchedPSL.Mfin S) t ≤ ρ' * C t :=
    fun ρ' hρ' t ht => Finset.sup'_le _ _ fun i _ => FracTruthSchedPSL.Mfin_load S ρ' hρ' ht i
  exact ⟨FracTruthSchedPSL.Mfin S, FracTruthSchedPSL.Mfin_feasible S,
    FracTruthSchedPSL.Mfin_truthful S, hload ρ hρ, hload, FracTruthSchedPSL.Mfin_eligible S,
    FracTruthSchedPSL.Mfin_uz S, FracTruthSchedPSL.Mfin_zti S, FracTruthSchedPSL.Mfin_symm S⟩
