-- Prove2me | solution 1 for BertsekasShreve.FiniteHorizon.dp_algorithm_optimal_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:27:16.193567+00:00
-- url     : https://prove2.me/submissions/547a6fac-624b-4721-bc44-97199d51cc78

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions



namespace BertsekasShreve.FiniteHorizon

open Model Filter Topology

namespace UOAux

variable {S C : Type*} (m : Model S C)

theorem comp_succ (π : m.Policy) (n : ℕ) (J : S → EReal) :
    m.comp π (n + 1) J = m.Tmu (π 0) (m.comp (π.shift 1) n J) := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    show m.comp π (n + 1) (m.Tmu (π (n + 1)) J) = _
    rw [ih]
    show _ = m.Tmu (π 0) (m.comp (π.shift 1) n (m.Tmu (π.shift 1 n) J))
    simp only [Policy.shift, Nat.add_comm 1 n]

theorem shift_shift (π : m.Policy) (i j : ℕ) : (π.shift i).shift j = π.shift (i + j) := by
  funext k; simp [Policy.shift, Nat.add_assoc]

theorem costN_shift_succ (J₀ : S → EReal) (π : m.Policy) (i n : ℕ) :
    m.costN J₀ (n + 1) (π.shift i) = m.Tmu (π i) (m.costN J₀ n (π.shift (i + 1))) := by
  unfold costN; rw [comp_succ, shift_shift]; rfl

theorem Tmu_mono (μ : m.Selector) {J J' : S → EReal} (h : J ≤ J') : m.Tmu μ J ≤ m.Tmu μ J' :=
  fun x => m.mono x _ (μ.2 x) J J' h

theorem T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J :=
  fun x => biInf_le (fun u => m.H x u J) (μ.2 x)

theorem T_mono {J J' : S → EReal} (h : J ≤ J') : m.T J ≤ m.T J' := by
  intro x
  exact iInf₂_mono fun u hu => m.mono x u hu J J' h

theorem iterT_le_comp (π : m.Policy) (n : ℕ) (J : S → EReal) : m.T^[n] J ≤ m.comp π n J := by
  induction n generalizing π with
  | zero => exact le_rfl
  | succ n ih =>
    rw [comp_succ, Function.iterate_succ_apply']
    exact (T_mono m (ih _)).trans (T_le_Tmu m _ _)

theorem iterT_le_optCostN (J₀ : S → EReal) (n : ℕ) : m.T^[n] J₀ ≤ m.optCostN J₀ n :=
  fun x => le_iInf fun π => iterT_le_comp m π n J₀ x

/-- a selector taking value `u` at `x`. -/
noncomputable def selAt (x : S) (u : C) (hu : u ∈ m.U x) : m.Selector := by
  classical
  exact ⟨fun y => if y = x then u else (m.U_nonempty y).some, fun y => by
    by_cases h : y = x
    · subst h; simpa using hu
    · simpa [h] using (m.U_nonempty y).some_mem⟩

theorem selAt_apply (x : S) (u : C) (hu : u ∈ m.U x) : (selAt m x u hu).1 x = u := by
  simp [selAt]

def cons (μ : m.Selector) (π : m.Policy) : m.Policy := fun n => Nat.casesOn n μ fun k => π k

theorem optCostN_succ_le_T_costN (J₀ : S → EReal) (n : ℕ) (π : m.Policy) :
    m.optCostN J₀ (n + 1) ≤ m.T (m.costN J₀ n π) := by
  intro x
  refine le_iInf₂ fun u hu => ?_
  have h1 : m.optCostN J₀ (n + 1) x ≤ m.costN J₀ (n + 1) (cons m (selAt m x u hu) π) x :=
    iInf_le _ _
  have h2 : m.costN J₀ (n + 1) (cons m (selAt m x u hu) π) =
      m.Tmu (selAt m x u hu) (m.costN J₀ n π) := by
    have hs : (cons m (selAt m x u hu) π).shift 1 = π := by
      funext k; simp [Policy.shift, cons, Nat.add_comm 1 k]
    unfold costN; rw [comp_succ, hs]; rfl
  rw [h2] at h1
  simpa [Tmu, selAt_apply] using h1

theorem iterT_eq_of_attained (J₀ : S → EReal) (N : ℕ) (π : m.Policy)
    (h : ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀) :
    ∀ j, j ≤ N → m.costN J₀ j (π.shift (N - j)) = m.T^[j] J₀ := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [costN_shift_succ, show N - (j + 1) + 1 = N - j by omega, ih (by omega)]
    have := h (N - (j + 1)) (by omega)
    rwa [show N - (N - (j + 1)) - 1 = j by omega, show N - (N - (j + 1)) = j + 1 by omega] at this

theorem uo_iff_core (J₀ : S → EReal) (N : ℕ) (π : m.Policy) :
    m.IsUniformlyNStageOptimal J₀ N π ↔
      ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀ := by
  constructor
  · intro hU
    -- show by induction on j ≤ N that costN j (shift (N-j)) = T^j J₀
    have key : ∀ j, j ≤ N → m.costN J₀ j (π.shift (N - j)) = m.T^[j] J₀ := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hopt := hU (N - (j + 1)) (by omega)
        rw [show N - (N - (j + 1)) = j + 1 by omega] at hopt
        have e1 : m.costN J₀ (j + 1) (π.shift (N - (j + 1))) =
            m.Tmu (π (N - (j + 1))) (m.T^[j] J₀) := by
          rw [costN_shift_succ, show N - (j + 1) + 1 = N - j by omega, ih (by omega)]
        apply le_antisymm
        · calc m.costN J₀ (j + 1) (π.shift (N - (j + 1))) = m.optCostN J₀ (j + 1) := hopt
            _ ≤ m.T (m.costN J₀ j (π.shift (N - j))) := optCostN_succ_le_T_costN m J₀ j _
            _ = m.T^[j + 1] J₀ := by rw [ih (by omega), Function.iterate_succ_apply']
        · rw [e1, Function.iterate_succ_apply']; exact T_le_Tmu m _ _
    intro k hk
    have e := key (N - k) (by omega)
    rw [show N - (N - k) = k by omega, show N - k = (N - k - 1) + 1 by omega,
      costN_shift_succ, show k + 1 = N - (N - k - 1) by omega, key _ (by omega)] at e
    rw [show N - k = (N - k - 1) + 1 by omega]
    exact e
  · intro h i hi
    have e := iterT_eq_of_attained m J₀ N π h (N - i) (by omega)
    rw [show N - (N - i) = i by omega] at e
    unfold IsNStageOptimal
    rw [e]
    apply le_antisymm (iterT_le_optCostN m J₀ _)
    intro x
    exact (iInf_le _ (π.shift i)).trans (le_of_eq (congrFun e x))

theorem exists_uo_iff_core (J₀ : S → EReal) (N : ℕ) :
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ m.U x, m.H x u (m.T^[k] J₀) = m.T^[k + 1] J₀ x) ∧
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) →
      m.optCostN J₀ N = m.T^[N] J₀) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨π, hπ⟩ x k hk
    have := ((uo_iff_core m J₀ N π).1 hπ) (N - 1 - k) (by omega)
    rw [show N - (N - 1 - k) - 1 = k by omega, show N - (N - 1 - k) = k + 1 by omega] at this
    exact ⟨(π (N - 1 - k)).1 x, (π (N - 1 - k)).2 x, congrFun this x⟩
  · intro h
    classical
    have hsel : ∀ k, ∃ μ : m.Selector, k < N → m.Tmu μ (m.T^[k] J₀) = m.T^[k + 1] J₀ := by
      intro k
      by_cases hk : k < N
      · choose u hu heq using fun x => h x k hk
        exact ⟨⟨u, hu⟩, fun _ => funext heq⟩
      · exact ⟨⟨fun y => (m.U_nonempty y).some, fun y => (m.U_nonempty y).some_mem⟩,
          fun h' => absurd h' hk⟩
    choose μ hμ using hsel
    refine ⟨fun i => μ (N - 1 - i), (uo_iff_core m J₀ N _).2 fun k hk => ?_⟩
    have := hμ (N - 1 - k) (by omega)
    rw [show N - 1 - k = N - k - 1 by omega, show N - k - 1 + 1 = N - k by omega] at this
    simpa [show N - 1 - k = N - k - 1 by omega] using this
  · rintro ⟨π, hπ⟩
    have e := iterT_eq_of_attained m J₀ N π ((uo_iff_core m J₀ N π).1 hπ) N le_rfl
    apply le_antisymm _ (iterT_le_optCostN m J₀ _)
    intro x
    exact (iInf_le _ (π.shift (N - N))).trans (le_of_eq (congrFun e x))

end UOAux

namespace DPAux

variable {S C : Type*} (m : Model S C)

theorem costN_cons (J₀ : S → EReal) (k : ℕ) (μ : m.Selector) (π : m.Policy) :
    m.costN J₀ (k + 1) (UOAux.cons m μ π) = m.Tmu μ (m.costN J₀ k π) := by
  have hs : (UOAux.cons m μ π).shift 1 = π := by
    funext j; simp [Policy.shift, UOAux.cons, Nat.add_comm 1 j]
  unfold costN; rw [UOAux.comp_succ, hs]; rfl

noncomputable def defPol : m.Policy :=
  fun _ => ⟨fun y => (m.U_nonempty y).some, fun y => (m.U_nonempty y).some_mem⟩

theorem F1_seq (J₀ : S → EReal) (N : ℕ) (hF1 : m.AssumptionF1)
    (hfin : ∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) :
    ∀ k, k ≤ N → ∃ πs : ℕ → m.Policy,
      (∀ n, m.costN J₀ k (πs (n + 1)) ≤ m.costN J₀ k (πs n)) ∧
      ∀ x, Tendsto (fun n => m.costN J₀ k (πs n) x) atTop (𝓝 (m.T^[k] J₀ x)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => defPol m, fun _ => le_rfl, fun x => tendsto_const_nhds⟩
  | succ k ih =>
    intro hk
    obtain ⟨πs, hanti, hlim⟩ := ih (by omega)
    set Jn : ℕ → S → EReal := fun n => m.costN J₀ k (πs n) with hJn
    set L : S → EReal := m.T^[k] J₀ with hL
    have hF : ∀ x, ∀ u ∈ m.U x, Tendsto (fun n => m.H x u (Jn n)) atTop (𝓝 (m.H x u L)) := by
      refine hF1 Jn hanti (fun x u hu => ?_) L hlim
      have := hfin x (UOAux.cons m (UOAux.selAt m x u hu) (πs 0)) (k + 1) (by omega) hk
      rw [costN_cons] at this
      simpa [Tmu, UOAux.selAt_apply] using this
    have hcand : ∀ x, ∃ v : ℕ → C, (∀ j, v j ∈ m.U x) ∧
        Tendsto (fun j => m.H x (v j) L) atTop (𝓝 (m.T L x)) := by
      intro x
      obtain ⟨w, -, hw, hwS⟩ := exists_seq_tendsto_sInf
        (S := (fun u => m.H x u L) '' m.U x) ((m.U_nonempty x).image _) (OrderBot.bddBelow _)
      rw [sInf_image] at hw
      choose v hv hveq using hwS
      refine ⟨v, hv, ?_⟩
      have : (fun j => m.H x (v j) L) = w := funext hveq
      rw [this]; exact hw
    choose v hvU hvlim using hcand
    have hJanti : ∀ x, Antitone (fun n => Jn n x) :=
      fun x => antitone_nat_of_succ_le fun n => hanti n x
    have hLle : ∀ n, L ≤ Jn n := fun n x => (hJanti x).le_of_tendsto (hlim x) n
    have hsel : ∀ n x, ∃ j ∈ Finset.range (n + 1),
        (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one
          (fun j => m.H x (v x j) (Jn n)) = m.H x (v x j) (Jn n) := fun n x =>
      Finset.exists_mem_eq_inf' Finset.nonempty_range_add_one _
    choose jj hjmem hjeq using hsel
    let μ : ℕ → m.Selector := fun n => ⟨fun x => v x (jj n x), fun x => hvU x _⟩
    let val : ℕ → S → EReal := fun n x => (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one
          (fun j => m.H x (v x j) (Jn n))
    have hcost : ∀ n, m.costN J₀ (k + 1) (UOAux.cons m (μ n) (πs n)) = val n := by
      intro n; rw [costN_cons]; funext x
      simp only [Tmu, val]
      rw [hjeq n x]
    refine ⟨fun n => UOAux.cons m (μ n) (πs n), ?_, ?_⟩
    · intro n x
      simp only [hcost]
      refine Finset.le_inf' _ _ fun j hj => ?_
      refine (Finset.inf'_le _ (Finset.mem_range.2 (show j < n + 1 + 1 by
        have := Finset.mem_range.1 hj; omega))).trans ?_
      exact m.mono x _ (hvU x j) _ _ (hanti n)
    · intro x
      simp only [hcost]
      have hvalanti : Antitone (fun n => val n x) := by
        refine antitone_nat_of_succ_le fun n => ?_
        refine Finset.le_inf' _ _ fun j hj => ?_
        refine (Finset.inf'_le _ (Finset.mem_range.2 (show j < n + 1 + 1 by
          have := Finset.mem_range.1 hj; omega))).trans ?_
        exact m.mono x _ (hvU x j) _ _ (hanti n)
      have h1 := tendsto_atTop_iInf hvalanti
      convert h1 using 2
      rw [Function.iterate_succ_apply']
      apply le_antisymm
      · refine le_iInf fun n => Finset.le_inf' _ _ fun j _ => ?_
        exact (biInf_le (fun u => m.H x u L) (hvU x j)).trans (m.mono x _ (hvU x j) _ _ (hLle n))
      · refine ge_of_tendsto (hvlim x) (Eventually.of_forall fun j => ?_)
        refine ge_of_tendsto (hF x _ (hvU x j)) (eventually_atTop.2 ⟨j, fun n hn => ?_⟩)
        exact (iInf_le _ n).trans (Finset.inf'_le _ (Finset.mem_range.2 (by omega)))

theorem partA (J₀ : S → EReal) (N : ℕ) (hF1 : m.AssumptionF1)
    (hfin : ∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) :
    m.optCostN J₀ N = m.T^[N] J₀ := by
  obtain ⟨πs, -, hlim⟩ := F1_seq m J₀ N hF1 hfin N le_rfl
  apply le_antisymm _ (UOAux.iterT_le_optCostN m J₀ N)
  intro x
  exact ge_of_tendsto' (hlim x) fun n => iInf_le _ _

theorem le_of_forall_pos (a b : EReal) (h : ∀ c : ℝ, 0 < c → a ≤ b + (c : EReal)) : a ≤ b := by
  by_contra hcon
  push_neg at hcon
  induction b using EReal.rec with
  | bot => have := h 1 one_pos; simp at this; exact absurd this (ne_of_gt hcon)
  | top => exact absurd hcon (not_lt.2 le_top)
  | coe t =>
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr1' : t < r := EReal.coe_lt_coe_iff.1 hr1
    have := h (r - t) (by linarith)
    rw [← EReal.coe_add, show t + (r - t) = r by ring] at this
    exact absurd hr2 (not_lt.2 this)

theorem add_lt_coe_iff (a : EReal) (c r : ℝ) : a + (c : EReal) < (r : EReal) ↔ a < ((r - c : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_add]; exact iff_of_true (EReal.bot_lt_coe _) (EReal.bot_lt_coe _)
  | top => simp
  | coe t =>
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]; constructor <;> intro <;> linarith

theorem T_add_le (J : S → EReal) (c δ : ℝ)
    (h : ∀ x, ∀ u ∈ m.U x, m.H x u (fun y => J y + (δ : EReal)) ≤ m.H x u J + (c : EReal)) (x : S) :
    m.T (fun y => J y + (δ : EReal)) x ≤ m.T J x + (c : EReal) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  rw [add_lt_coe_iff] at hr1
  simp only [Model.T] at hr1
  obtain ⟨u, hu⟩ := iInf_lt_iff.1 hr1
  obtain ⟨hu, hlt⟩ := iInf_lt_iff.1 hu
  have h2 : m.H x u J + (c : EReal) < r := (add_lt_coe_iff _ _ _).2 hlt
  have h3 : m.T (fun y => J y + (δ : EReal)) x ≤ m.H x u (fun y => J y + (δ : EReal)) :=
    biInf_le (fun u => m.H x u (fun y => J y + (δ : EReal))) hu
  exact absurd (h3.trans ((h x u hu).trans h2.le)) (not_le.2 hr2)

theorem exists_near (J : S → EReal) (x : S) (hx : m.T J x ≠ ⊥) (c : ℝ) (hc : 0 < c) :
    ∃ u ∈ m.U x, m.H x u J ≤ m.T J x + (c : EReal) := by
  obtain ⟨u0, hu0⟩ := m.U_nonempty x
  induction h : m.T J x using EReal.rec with
  | bot => exact absurd h hx
  | top => exact ⟨u0, hu0, by simp⟩
  | coe t =>
    have : m.T J x < ((t + c : ℝ) : EReal) := by rw [h]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    simp only [Model.T] at this
    obtain ⟨u, hu⟩ := iInf_lt_iff.1 this
    obtain ⟨hu, hlt⟩ := iInf_lt_iff.1 hu
    exact ⟨u, hu, by rw [← EReal.coe_add]; exact hlt.le⟩

theorem partB (J₀ : S → EReal) (N : ℕ) (hF2 : m.AssumptionF2)
    (hfin : ∀ x (k : ℕ), 1 ≤ k → k ≤ N → m.optCostN J₀ k x ≠ ⊥) :
    ∀ k, k ≤ N → m.optCostN J₀ k = m.T^[k] J₀ ∧
      ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy, m.costN J₀ k π ≤ fun x => m.optCostN J₀ k x + (ε : EReal) := by
  obtain ⟨α, hα, hF⟩ := hF2
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : m.optCostN J₀ 0 = J₀ := by
      funext x; simp only [optCostN, costN, comp]
      haveI : Nonempty m.Policy := ⟨defPol m⟩
      exact iInf_const
    refine ⟨h0, fun ε hε => ⟨defPol m, fun x => ?_⟩⟩
    rw [h0]; exact le_add_of_nonneg_right (EReal.coe_nonneg.2 hε.le)
  | succ k ih =>
    intro hk
    obtain ⟨hk1, hk2⟩ := ih (by omega)
    -- key bound: optCost (k+1) ≤ T(optCost k) + α δ
    have hstep : ∀ δ : ℝ, 0 < δ → ∀ π : m.Policy,
        m.costN J₀ k π ≤ (fun x => m.optCostN J₀ k x + (δ : EReal)) →
        ∀ μ : m.Selector, ∀ x,
          m.costN J₀ (k + 1) (UOAux.cons m μ π) x ≤
            m.H x (μ.1 x) (m.optCostN J₀ k) + ((α * δ : ℝ) : EReal) := by
      intro δ hδ π hπ μ x
      rw [costN_cons]
      exact (m.mono x _ (μ.2 x) _ _ hπ).trans ((hF δ hδ _ x _ (μ.2 x)).2)
    have hT : m.T^[k + 1] J₀ = m.T (m.optCostN J₀ k) := by
      rw [Function.iterate_succ_apply', hk1]
    have heq : m.optCostN J₀ (k + 1) = m.T^[k + 1] J₀ := by
      apply le_antisymm _ (UOAux.iterT_le_optCostN m J₀ _)
      intro x
      rw [hT]
      apply le_of_forall_pos
      intro c hc
      obtain ⟨π, hπ⟩ := hk2 (c / α) (div_pos hc hα)
      refine (UOAux.optCostN_succ_le_T_costN m J₀ k π x).trans ?_
      refine (UOAux.T_mono m hπ x).trans ?_
      refine T_add_le m _ (α * (c / α)) (c / α) (fun x u hu => (hF _ (div_pos hc hα) _ x u hu).2) x |>.trans ?_
      rw [show α * (c / α) = c by field_simp]
    refine ⟨heq, fun ε hε => ?_⟩
    obtain ⟨π, hπ⟩ := hk2 (ε / 2 / α) (div_pos (half_pos hε) hα)
    have hsel : ∀ x, ∃ u ∈ m.U x, m.H x u (m.optCostN J₀ k) ≤
        m.T (m.optCostN J₀ k) x + ((ε / 2 : ℝ) : EReal) := by
      intro x
      apply exists_near m _ x _ _ (half_pos hε)
      rw [← hT, ← heq]; exact hfin x (k + 1) (by omega) hk
    choose u hu hule using hsel
    refine ⟨UOAux.cons m ⟨u, hu⟩ π, fun x => ?_⟩
    refine (hstep _ (div_pos (half_pos hε) hα) π hπ ⟨u, hu⟩ x).trans ?_
    rw [show α * (ε / 2 / α) = ε / 2 by field_simp]
    refine (add_le_add (hule x) le_rfl).trans (le_of_eq ?_)
    rw [heq, hT, add_assoc, ← EReal.coe_add, show ε / 2 + ε / 2 = ε by ring]

end DPAux

theorem dp_algorithm_optimal_cost_core {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (N : ℕ) :
    (m.AssumptionF1 →
      (∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) →
      m.optCostN J₀ N = m.T^[N] J₀) ∧
    (m.AssumptionF2 →
      (∀ x (k : ℕ), 1 ≤ k → k ≤ N → m.optCostN J₀ k x ≠ ⊥) →
      m.optCostN J₀ N = m.T^[N] J₀ ∧
        ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
          m.optCostN J₀ N ≤ m.costN J₀ N π ∧
            m.costN J₀ N π ≤ fun x => m.optCostN J₀ N x + (ε : EReal)) := by
  refine ⟨fun hF1 hfin => DPAux.partA m J₀ N hF1 hfin, fun hF2 hfin => ?_⟩
  obtain ⟨h1, h2⟩ := DPAux.partB m J₀ N hF2 hfin N le_rfl
  refine ⟨h1, fun ε hε => ?_⟩
  obtain ⟨π, hπ⟩ := h2 ε hε
  exact ⟨π, fun x => iInf_le _ π, hπ⟩

end BertsekasShreve.FiniteHorizon

open BertsekasShreve.FiniteHorizon
open Model

theorem solution {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) :
    (m.AssumptionF1 →
      (∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) →
      m.optCostN J₀ N = m.T^[N] J₀) ∧
    (m.AssumptionF2 →
      (∀ x (k : ℕ), 1 ≤ k → k ≤ N → m.optCostN J₀ k x ≠ ⊥) →
      m.optCostN J₀ N = m.T^[N] J₀ ∧
        ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
          m.optCostN J₀ N ≤ m.costN J₀ N π ∧
            m.costN J₀ N π ≤ fun x => m.optCostN J₀ N x + (ε : EReal)) := by
  exact dp_algorithm_optimal_cost_core m J₀ N
