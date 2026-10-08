-- Prove2me | solution 1 for BertsekasShreve.Monotone.prop5_11_accumulation_points_optimal
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T23:04:34.939902+00:00
-- url     : https://prove2.me/submissions/32171cbc-d45c-48fd-ba5d-ff2a36c5096c

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me a3a0f45f-69ff-4bc7-b0ea-7620ab86783f.
-- Reused accepted contributions are attributed beside their full proof bodies.
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Increase_Epigraph
import Definitions.Def_MonotoneDP_Increase_Model
import Mathlib
import Mathlib.Tactic
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false


-- BEGIN MODULE CompactClusters
section

set_option autoImplicit false

open Filter Topology

namespace BertsekasShreve.Monotone.Proof

variable {C : Type*} [TopologicalSpace C] [T2Space C]

omit [TopologicalSpace C] [T2Space C] in
lemma eventually_mem_sublevel (U : Set C) (F : ℕ → C → EReal)
    (hm : ∀ u ∈ U, Monotone (fun k => F k u)) (kbar : ℕ) (lam : ℝ)
    (u : ℕ → C) (hu : ∀ k, u k ∈ U)
    (hb : ∀ k, kbar ≤ k → F k (u k) ≤ (lam : EReal)) (N : ℕ) :
    ∀ᶠ k in atTop, u k ∈ {v | v ∈ U ∧ F N v ≤ (lam : EReal)} := by
  filter_upwards [eventually_ge_atTop (max kbar N)] with k hk
  exact ⟨hu k, (hm (u k) (hu k) (le_trans (le_max_right _ _) hk)).trans
    (hb k (le_trans (le_max_left _ _) hk))⟩

omit [T2Space C] in
lemma exists_cluster_of_sublevels (U : Set C) (F : ℕ → C → EReal)
    (hm : ∀ u ∈ U, Monotone (fun k => F k u)) (kbar : ℕ) (lam : ℝ)
    (hcpt : IsCompact {v | v ∈ U ∧ F kbar v ≤ (lam : EReal)})
    (u : ℕ → C) (hu : ∀ k, u k ∈ U)
    (hb : ∀ k, kbar ≤ k → F k (u k) ≤ (lam : EReal)) :
    ∃ v : C, MapClusterPt v atTop u := by
  have he := eventually_mem_sublevel U F hm kbar lam u hu hb kbar
  obtain ⟨v, _, hv⟩ := hcpt.exists_mapClusterPt_of_frequently he.frequently
  exact ⟨v, hv⟩

lemma cluster_mem_and_le (U : Set C) (F : ℕ → C → EReal)
    (hm : ∀ u ∈ U, Monotone (fun k => F k u)) (kbar : ℕ) (lam : ℝ)
    (hcpt : ∀ N, kbar ≤ N → IsCompact {v | v ∈ U ∧ F N v ≤ (lam : EReal)})
    (u : ℕ → C) (hu : ∀ k, u k ∈ U)
    (hb : ∀ k, kbar ≤ k → F k (u k) ≤ (lam : EReal))
    (v : C) (hv : MapClusterPt v atTop u) :
    v ∈ U ∧ ∀ N, F N v ≤ (lam : EReal) := by
  have hall (N : ℕ) (hN : kbar ≤ N) : v ∈ U ∧ F N v ≤ (lam : EReal) :=
    (hcpt N hN).isClosed.mem_of_mapClusterPt hv
      (eventually_mem_sublevel U F hm kbar lam u hu hb N)
  have hvU := (hall kbar le_rfl).1
  refine ⟨hvU, fun N => ?_⟩
  exact (hm v hvU (le_max_left N kbar)).trans (hall (max N kbar) (le_max_right _ _)).2

end BertsekasShreve.Monotone.Proof

end
-- END MODULE CompactClusters

-- BEGIN MODULE ModelClusters
section

set_option autoImplicit false

open Filter Topology MonotoneDP.Increase

namespace BertsekasShreve.Monotone.Proof

variable {S C : Type*} [TopologicalSpace C] [T2Space C]

omit [TopologicalSpace C] [T2Space C] in
lemma optimal_value_real (m : Model S C) (hJ : m.Jbar ≤ m.Jstar)
    (x : S) (hx : m.Jstar x < ⊤) : ((m.Jstar x).toReal : EReal) = m.Jstar x := by
  apply EReal.coe_toReal hx.ne
  intro hb
  have he := hJ x
  rw [hb] at he
  exact m.Jbar_ne_bot x (le_bot_iff.mp he)

omit [TopologicalSpace C] [T2Space C] in
lemma minimizing_stage_bound (m : Model S C)
    (hle : ∀ k, (m.T^[k] m.Jbar) ≤ m.Jstar) (kbar : ℕ)
    (π : m.Policy) (hπ : ∀ k, kbar ≤ k → m.Tmu (π k) (m.T^[k] m.Jbar) = m.T^[k+1] m.Jbar)
    (x : S) (k : ℕ) (hk : kbar ≤ k) :
    m.H x ((π k).1 x) (m.T^[k] m.Jbar) ≤ m.Jstar x := by
  have he := congrFun (hπ k hk) x
  exact he.trans_le (hle (k+1) x)

omit [T2Space C] in
lemma minimizing_controls_cluster_exists (m : Model S C)
    (hmono : Monotone (fun k => m.T^[k] m.Jbar))
    (hJ : m.Jbar ≤ m.Jstar) (hle : ∀ k, (m.T^[k] m.Jbar) ≤ m.Jstar)
    (kbar : ℕ)
    (hcpt : ∀ x (lam : ℝ) k, kbar ≤ k → IsCompact {u | u ∈ m.U x ∧
      m.H x u (m.T^[k] m.Jbar) ≤ (lam : EReal)})
    (π : m.Policy) (hπ : ∀ k, kbar ≤ k → m.Tmu (π k) (m.T^[k] m.Jbar) = m.T^[k+1] m.Jbar)
    (x : S) (hx : m.Jstar x < ⊤) :
    ∃ u : C, MapClusterPt u atTop (fun k => (π k).1 x) := by
  have hr := optimal_value_real m hJ x hx
  apply exists_cluster_of_sublevels (m.U x) (fun k u => m.H x u (m.T^[k] m.Jbar))
    (fun u hu k l hkl => m.mono x u hu _ _ (hmono hkl)) kbar (m.Jstar x).toReal
    (hcpt x _ kbar le_rfl) (fun k => (π k).1 x) (fun k => (π k).2 x)
  intro k hk
  rw [hr]
  exact minimizing_stage_bound m hle kbar π hπ x k hk

lemma cluster_control_bellman_le (m : Model S C) (hI1 : m.AssumptionI1)
    (hmono : Monotone (fun k => m.T^[k] m.Jbar))
    (hJ : m.Jbar ≤ m.Jstar) (hle : ∀ k, (m.T^[k] m.Jbar) ≤ m.Jstar)
    (hconv : m.Jinf = m.Jstar) (kbar : ℕ)
    (hcpt : ∀ x (lam : ℝ) k, kbar ≤ k → IsCompact {u | u ∈ m.U x ∧
      m.H x u (m.T^[k] m.Jbar) ≤ (lam : EReal)})
    (π : m.Policy) (hπ : ∀ k, kbar ≤ k → m.Tmu (π k) (m.T^[k] m.Jbar) = m.T^[k+1] m.Jbar)
    (x : S) (hx : m.Jstar x < ⊤) (u : C)
    (hu : MapClusterPt u atTop (fun k => (π k).1 x)) :
    u ∈ m.U x ∧ m.H x u m.Jstar ≤ m.Jstar x := by
  have hr := optimal_value_real m hJ x hx
  have hbound (k : ℕ) (hk : kbar ≤ k) :
      m.H x ((π k).1 x) (m.T^[k] m.Jbar) ≤ ((m.Jstar x).toReal : EReal) := by
    rw [hr]
    exact minimizing_stage_bound m hle kbar π hπ x k hk
  obtain ⟨huU, huN⟩ := cluster_mem_and_le (m.U x)
    (fun k u => m.H x u (m.T^[k] m.Jbar))
    (fun u hu k l hkl => m.mono x u hu _ _ (hmono hkl)) kbar (m.Jstar x).toReal
    (hcpt x _) (fun k => (π k).1 x) (fun k => (π k).2 x) hbound u hu
  refine ⟨huU, ?_⟩
  have hmH : Monotone (fun k => m.H x u (m.T^[k] m.Jbar)) :=
    fun k l hkl => m.mono x u huU _ _ (hmono hkl)
  have hlim : limUnder atTop (fun k => m.H x u (m.T^[k] m.Jbar)) ≤ m.Jstar x := by
    rw [(tendsto_atTop_iSup hmH).limUnder_eq]
    exact iSup_le (fun k => (huN k).trans_eq hr)
  have he := hI1 (fun k => m.T^[k] m.Jbar)
    (fun k => by simpa using hmono (Nat.zero_le k))
    (fun k => hmono (Nat.le_succ k)) x u huU
  change limUnder atTop (fun k => m.H x u (m.T^[k] m.Jbar)) = m.H x u m.Jinf at he
  rw [hconv] at he
  rwa [he] at hlim

end BertsekasShreve.Monotone.Proof

end
-- END MODULE ModelClusters

-- BEGIN MODULE AttributedCompactMin
section
-- Prove2me | solution 1 for MonotoneDP.Increase.lemma3_compact_sublevel_min
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:06:35.655265+00:00
-- url     : https://prove2.me/submissions/0e6dc7aa-8f83-48e5-a644-c75d270adafe


theorem MonotoneDP.Increase.lemma3_compact_sublevel_min {C : Type*} [TopologicalSpace C] [T2Space C]
    (f : C → EReal) (U : Set C) (hU : U.Nonempty)
    (hcpt : ∀ lam : ℝ, IsCompact {u ∈ U | f u ≤ (lam : EReal)}) :
    ∃ u ∈ U, IsMinOn f U u := by
  by_cases htop : ∀ u ∈ U, f u = ⊤
  · obtain ⟨u, hu⟩ := hU
    refine ⟨u, hu, ?_⟩
    intro x hx
    show f u ≤ f x
    rw [htop u hu, htop x hx]
  · push Not at htop
    obtain ⟨u0, hu0U, hu0⟩ := htop
    have hmemT : ∀ x ∈ U, f x ≠ ⊤ → ∃ lam : ℝ,
        ({u ∈ U | f u ≤ (lam : EReal)}).Nonempty := by
      intro x hx hxt
      by_cases hb : f x = ⊥
      · exact ⟨0, ⟨x, hx, by rw [hb]; exact bot_le⟩⟩
      · exact ⟨(f x).toReal, ⟨x, hx, by rw [EReal.coe_toReal hxt hb]⟩⟩
    obtain ⟨lam0, hlam0⟩ := hmemT u0 hu0U hu0
    let T : Set ℝ := {lam : ℝ | ({u ∈ U | f u ≤ (lam : EReal)}).Nonempty}
    have hlam0T : lam0 ∈ T := hlam0
    have hne : Nonempty T := ⟨⟨lam0, hlam0T⟩⟩
    have hint : (⋂ lam : T, {u ∈ U | f u ≤ ((lam : ℝ) : EReal)}).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ ?_ ?_ ?_
      · intro a b
        rcases le_total (a : ℝ) (b : ℝ) with h | h
        · refine ⟨a, subset_rfl, fun u hu => ⟨hu.1, le_trans hu.2 ?_⟩⟩
          exact EReal.coe_le_coe_iff.mpr h
        · refine ⟨b, fun u hu => ⟨hu.1, le_trans hu.2 ?_⟩, subset_rfl⟩
          exact EReal.coe_le_coe_iff.mpr h
      · intro i; exact i.2
      · intro i; exact hcpt _
      · intro i; exact (hcpt _).isClosed
    obtain ⟨u, hu⟩ := hint
    have huU : u ∈ U := (Set.mem_iInter.mp hu ⟨lam0, hlam0T⟩).1
    refine ⟨u, huU, ?_⟩
    intro x hx
    show f u ≤ f x
    by_cases hxt : f x = ⊤
    · rw [hxt]; exact le_top
    · by_cases hb : f x = ⊥
      · have hall : ∀ r : ℝ, f u ≤ (r : EReal) := by
          intro r
          have hrT : r ∈ T := ⟨x, hx, by rw [hb]; exact bot_le⟩
          exact (Set.mem_iInter.mp hu ⟨r, hrT⟩).2
        have hfu : f u = ⊥ := by
          rcases eq_or_ne (f u) ⊤ with h | h
          · exfalso
            have h0 := hall 0
            rw [h] at h0
            simp at h0
          · rcases eq_or_ne (f u) ⊥ with h' | h'
            · exact h'
            · exfalso
              set r := (f u).toReal with hr
              have hc : ((r : ℝ) : EReal) = f u := EReal.coe_toReal h h'
              have h2 := hall (r - 1)
              rw [← hc, EReal.coe_le_coe_iff] at h2
              linarith
        rw [hfu, hb]
      · have hrT : (f x).toReal ∈ T := ⟨x, hx, by rw [EReal.coe_toReal hxt hb]⟩
        have h1 := (Set.mem_iInter.mp hu ⟨(f x).toReal, hrT⟩).2
        rwa [EReal.coe_toReal hxt hb] at h1

end
-- END MODULE AttributedCompactMin

-- BEGIN MODULE StagePolicy
section

set_option autoImplicit false

namespace BertsekasShreve.Monotone.Proof

open MonotoneDP.Increase

theorem exists_stage_minimizing_policy {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : Model S C) (kbar : ℕ)
    (hcpt : ∀ x : S, ∀ lam : ℝ, ∀ k : ℕ, kbar ≤ k →
      IsCompact {u | u ∈ m.U x ∧ m.H x u ((m.T)^[k] m.Jbar) ≤ (lam : EReal)}) :
    ∃ π : m.Policy, ∀ k : ℕ, kbar ≤ k →
      m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k+1] m.Jbar := by
  classical
  have hex : ∀ k : ℕ, ∀ x : S, ∃ u ∈ m.U x, kbar ≤ k →
      m.H x u ((m.T)^[k] m.Jbar) = m.T ((m.T)^[k] m.Jbar) x := by
    intro k x
    by_cases hk : kbar ≤ k
    · obtain ⟨u, hu, hmin⟩ := lemma3_compact_sublevel_min
        (fun u => m.H x u ((m.T)^[k] m.Jbar)) (m.U x) (m.U_nonempty x)
        (fun lam => hcpt x lam k hk)
      refine ⟨u, hu, fun _ => le_antisymm ?_ ?_⟩
      · exact le_iInf (fun v => le_iInf (fun hv => hmin hv))
      · exact iInf_le_of_le u (iInf_le_of_le hu le_rfl)
    · obtain ⟨u, hu⟩ := m.U_nonempty x
      exact ⟨u, hu, fun h => (hk h).elim⟩
  choose f hfU hfH using hex
  refine ⟨fun k => ⟨f k, hfU k⟩, ?_⟩
  intro k hk
  funext x
  simpa only [Model.Tmu, Function.iterate_succ_apply'] using hfH k x hk

end BertsekasShreve.Monotone.Proof

end
-- END MODULE StagePolicy

-- BEGIN MODULE AttributedDPLimit
section
-- Prove2me | solution 1 for MonotoneDP.Increase.prop10_dp_limit_le_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:06:30.600975+00:00
-- url     : https://prove2.me/submissions/751671a2-6317-48af-b441-0cb2ecfe13aa


namespace MonotoneDP.Increase

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

theorem aux_p10_Tmu_mono (μ : m.Selector) : Monotone (m.Tmu μ) := by
  intro J J' h x
  exact m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_p10_T_mono : Monotone m.T := by
  intro J J' h x
  unfold T
  exact iInf₂_mono (fun u hu => m.mono x u hu J J' h)

theorem aux_p10_comp_mono (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => intro J J' h; simpa [comp] using h
  | succ N ih =>
    intro J J' h
    simp only [comp]
    exact ih (m.aux_p10_Tmu_mono (π N) h)

theorem aux_p10_T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J := by
  intro x
  exact iInf₂_le (μ.1 x) (μ.2 x)

theorem aux_p10_iter_le_comp (π : m.Policy) (N : ℕ) : ∀ J, (m.T)^[N] J ≤ m.comp π N J := by
  induction N with
  | zero => intro J; simp [comp]
  | succ N ih =>
    intro J
    rw [Function.iterate_succ_apply]
    simp only [comp]
    calc (m.T)^[N] (m.T J) ≤ (m.T)^[N] (m.Tmu (π N) J) :=
          (m.aux_p10_T_mono.iterate N) (m.aux_p10_T_le_Tmu _ _)
      _ ≤ _ := ih _

/-- The shifted policy `{μ₁, μ₂, …}`. -/
def aux_p10_shift (π : m.Policy) : m.Policy := fun k => π (k + 1)

theorem aux_p10_comp_succ (π : m.Policy) (N : ℕ) : ∀ J,
    m.comp π (N + 1) J = m.Tmu (π 0) (m.comp (m.aux_p10_shift π) N J) := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

variable {m}

theorem aux_p10_Jbar_le_Tmu (hI : m.AssumptionI) (μ : m.Selector) :
    m.Jbar ≤ m.Tmu μ m.Jbar :=
  fun x => hI x (μ.1 x) (μ.2 x)

theorem aux_p10_Jbar_le_T (hI : m.AssumptionI) : m.Jbar ≤ m.T m.Jbar :=
  fun x => le_iInf₂ (fun u hu => hI x u hu)

theorem aux_p10_comp_Jbar_mono (hI : m.AssumptionI) (π : m.Policy) :
    Monotone (fun N => m.comp π N m.Jbar) := by
  apply monotone_nat_of_le_succ
  intro N
  show m.comp π N m.Jbar ≤ m.comp π N (m.Tmu (π N) m.Jbar)
  exact m.aux_p10_comp_mono π N (aux_p10_Jbar_le_Tmu hI _)

theorem aux_p10_Jpi_eq (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨆ N, m.comp π N m.Jbar x := by
  unfold Jpi
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_p10_comp_Jbar_mono hI π hab x

theorem aux_p10_iter_mono (hI : m.AssumptionI) : Monotone (fun N => (m.T)^[N] m.Jbar) :=
  Monotone.monotone_iterate_of_le_map m.aux_p10_T_mono (aux_p10_Jbar_le_T hI)

theorem aux_p10_Jinf_eq (hI : m.AssumptionI) (x : S) :
    m.Jinf x = ⨆ N, (m.T)^[N] m.Jbar x := by
  unfold Jinf
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_p10_iter_mono hI hab x

theorem aux_p10_Jbar_le_Jpi (hI : m.AssumptionI) (π : m.Policy) : m.Jbar ≤ m.Jpi π := by
  intro x
  rw [aux_p10_Jpi_eq hI]
  exact le_iSup (fun N => m.comp π N m.Jbar x) 0

theorem aux_p10_Jbar_le_Jstar (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar :=
  fun x => le_iInf (fun π => aux_p10_Jbar_le_Jpi hI π x)

theorem aux_p10_Jbar_le_Jinf (hI : m.AssumptionI) : m.Jbar ≤ m.Jinf := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  exact le_iSup (fun N => (m.T)^[N] m.Jbar x) 0

theorem aux_p10_Jinf_le_Jstar (hI : m.AssumptionI) : m.Jinf ≤ m.Jstar := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  refine iSup_le (fun N => le_iInf (fun π => ?_))
  rw [aux_p10_Jpi_eq hI]
  exact le_trans (m.aux_p10_iter_le_comp π N m.Jbar x)
    (le_iSup (fun N => m.comp π N m.Jbar x) N)

theorem aux_p10_Jinf_le_TJinf (hI : m.AssumptionI) : m.Jinf ≤ m.T m.Jinf := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  refine iSup_le (fun N => ?_)
  have hle : (m.T)^[N] m.Jbar ≤ m.Jinf := by
    intro y
    rw [aux_p10_Jinf_eq hI]
    exact le_iSup (fun N => (m.T)^[N] m.Jbar y) N
  calc (m.T)^[N] m.Jbar x ≤ (m.T)^[N + 1] m.Jbar x := aux_p10_iter_mono hI (Nat.le_succ N) x
    _ = m.T ((m.T)^[N] m.Jbar) x := by rw [Function.iterate_succ_apply']
    _ ≤ m.T m.Jinf x := m.aux_p10_T_mono hle x

theorem aux_p10_TJstar_le (hI : m.AssumptionI) (hI1 : m.AssumptionI1) :
    m.T m.Jstar ≤ m.Jstar := by
  intro x
  refine le_iInf (fun π => ?_)
  set π' := m.aux_p10_shift π with hπ'
  set u := (π 0).1 x with hu_def
  have hu : u ∈ m.U x := (π 0).2 x
  have hmono := aux_p10_comp_Jbar_mono hI π'
  have hlim := hI1 (fun k => m.comp π' k m.Jbar) (fun k => hmono (Nat.zero_le k))
    (fun k => hmono (Nat.le_succ k)) x u hu
  have hsup : limUnder atTop (fun k => m.H x u (m.comp π' k m.Jbar)) =
      ⨆ k, m.H x u (m.comp π' k m.Jbar) := by
    apply Tendsto.limUnder_eq
    apply tendsto_atTop_iSup
    intro a b hab
    exact m.mono x u hu _ _ (hmono hab)
  calc m.T m.Jstar x ≤ m.H x u m.Jstar := iInf₂_le u hu
    _ ≤ m.H x u (m.Jpi π') := m.mono x u hu _ _ (fun y => iInf_le (fun π => m.Jpi π y) π')
    _ = ⨆ k, m.H x u (m.comp π' k m.Jbar) := by rw [← hsup, hlim]; rfl
    _ ≤ m.Jpi π x := by
      rw [aux_p10_Jpi_eq hI]
      refine iSup_le (fun k => ?_)
      have : m.comp π (k + 1) m.Jbar x = m.H x u (m.comp π' k m.Jbar) := by
        rw [aux_p10_comp_succ]; rfl
      rw [← this]
      exact le_iSup (fun N => m.comp π N m.Jbar x) (k + 1)

theorem aux_p10_min (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) (J' : S → EReal)
    (hbar : m.Jbar ≤ J') (hT : m.T J' ≤ J') : m.Jstar ≤ J' := by
  obtain ⟨α, hα, hI2⟩ := hI2
  intro x
  have key : ∀ ε : ℝ, 0 < ε → m.Jstar x ≤ J' x + (ε : EReal) := by
    intro ε hε
    set a : ℕ → ℝ := fun k => ε / (α + 1) ^ k with ha
    set δ : ℕ → ℝ := fun k => ε / (α + 1) ^ (k + 1) with hδ
    have hapos : ∀ k, 0 < a k := fun k => by simp only [ha]; positivity
    have hδpos : ∀ k, 0 < δ k := fun k => by simp only [hδ]; positivity
    have hrel : ∀ k, δ k + α * a (k + 1) = a k := by
      intro k
      simp only [ha, hδ]
      have h1 : (0 : ℝ) < α + 1 := by linarith
      field_simp
      ring
    have hex : ∀ k y, ∃ u ∈ m.U y, m.H y u J' ≤ J' y + (δ k : EReal) := by
      intro k y
      by_cases htop : J' y = ⊤
      · obtain ⟨u, hu⟩ := m.U_nonempty y
        exact ⟨u, hu, by rw [htop, EReal.top_add_coe]; exact le_top⟩
      · have hbot : J' y ≠ ⊥ := ne_bot_of_le_ne_bot (m.Jbar_ne_bot y) (hbar y)
        have hlt0 : J' y < J' y + (δ k : EReal) := by
          rw [← EReal.coe_toReal htop hbot, ← EReal.coe_add]
          exact_mod_cast (by linarith [hδpos k] : (J' y).toReal < (J' y).toReal + δ k)
        have hlt : m.T J' y < J' y + (δ k : EReal) := lt_of_le_of_lt (hT y) hlt0
        obtain ⟨u, hu, h⟩ : ∃ u ∈ m.U y, m.H y u J' < J' y + (δ k : EReal) := by
          simpa [T, iInf_lt_iff] using hlt
        exact ⟨u, hu, h.le⟩
    choose f hfU hfH using hex
    let π : m.Policy := fun k => ⟨f k, hfU k⟩
    have hstep : ∀ k, m.Tmu (π k) (fun y => J' y + (a (k + 1) : EReal)) ≤
        fun y => J' y + (a k : EReal) := by
      intro k y
      have h1 := (hI2 (a (k + 1)) (hapos _) J' hbar y (f k y) (hfU k y)).2
      calc m.Tmu (π k) (fun y => J' y + (a (k + 1) : EReal)) y
          = m.H y (f k y) (fun y => J' y + (a (k + 1) : EReal)) := rfl
        _ ≤ m.H y (f k y) J' + ((α * a (k + 1) : ℝ) : EReal) := h1
        _ ≤ (J' y + (δ k : EReal)) + ((α * a (k + 1) : ℝ) : EReal) := by
          gcongr
          exact hfH k y
        _ = J' y + (a k : EReal) := by rw [add_assoc, ← EReal.coe_add, hrel]
    have hind : ∀ N, m.comp π N (fun y => J' y + (a N : EReal)) ≤
        fun y => J' y + (a 0 : EReal) := by
      intro N
      induction N with
      | zero => exact le_refl _
      | succ N ih =>
        calc m.comp π (N + 1) (fun y => J' y + (a (N + 1) : EReal))
            = m.comp π N (m.Tmu (π N) (fun y => J' y + (a (N + 1) : EReal))) := rfl
          _ ≤ m.comp π N (fun y => J' y + (a N : EReal)) := m.aux_p10_comp_mono π N (hstep N)
          _ ≤ _ := ih
    have hJ'le : ∀ N, J' ≤ fun y => J' y + (a N : EReal) := by
      intro N y
      exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (hapos N).le)
    calc m.Jstar x ≤ m.Jpi π x := iInf_le (fun π => m.Jpi π x) π
      _ = ⨆ N, m.comp π N m.Jbar x := aux_p10_Jpi_eq hI π x
      _ ≤ J' x + (a 0 : EReal) := by
        refine iSup_le (fun N => ?_)
        exact (m.aux_p10_comp_mono π N (hbar.trans (hJ'le N))).trans (hind N) x
      _ = J' x + (ε : EReal) := by simp [ha]
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have htop : J' x ≠ ⊤ := ne_top_of_lt hz
  have hbot : J' x ≠ ⊥ := ne_bot_of_le_ne_bot (m.Jbar_ne_bot x) (hbar x)
  have hz' : (J' x).toReal < z := by
    rw [← EReal.coe_toReal htop hbot] at hz
    exact_mod_cast hz
  have := key (z - (J' x).toReal) (by linarith)
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_add] at this
  simpa using this

theorem aux_p10_TJstar_eq (hI : m.AssumptionI) (hI1 : m.AssumptionI1)
    (hI2 : ∃ α : ℝ, m.AssumptionI2 α) : m.T m.Jstar = m.Jstar := by
  have h1 := aux_p10_TJstar_le hI hI1
  apply le_antisymm h1
  apply aux_p10_min hI hI2
  · exact (aux_p10_Jbar_le_T hI).trans (m.aux_p10_T_mono (aux_p10_Jbar_le_Jstar hI))
  · exact m.aux_p10_T_mono h1

end Model

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem MonotoneDP.Increase.prop10_dp_limit_le_optimal {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (m.Jinf ≤ m.T m.Jinf ∧ m.T m.Jinf ≤ m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ∧
      ((m.Jinf = m.T m.Jinf ∧ m.T m.Jinf = m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ↔
        m.Jinf = m.T m.Jinf) := by
  have hstar := Model.aux_p10_TJstar_eq hI hI1 hI2
  have hle := Model.aux_p10_Jinf_le_Jstar hI
  refine ⟨⟨Model.aux_p10_Jinf_le_TJinf hI, m.aux_p10_T_mono hle, hstar⟩, ?_⟩
  constructor
  · exact fun h => h.1
  · intro h
    have hge : m.Jstar ≤ m.Jinf :=
      Model.aux_p10_min hI hI2 m.Jinf (Model.aux_p10_Jbar_le_Jinf hI) (le_of_eq h.symm)
    have heq : m.Jinf = m.Jstar := le_antisymm hle hge
    exact ⟨h, by rw [heq], hstar⟩

end
-- END MODULE AttributedDPLimit

-- BEGIN MODULE AttributedEpigraph
section
-- Prove2me | solution 1 for MonotoneDP.Increase.lemma2_projection_epigraph
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:53:49.579324+00:00
-- url     : https://prove2.me/submissions/fd407f2a-b95d-49fa-aefd-6674acc8eece


namespace MonotoneDP.Increase

open Filter Topology

/-- Unfolding `T^[k]` for `k ≥ 1`. -/
theorem aux_l2p_iter {S C : Type*} (m : Model S C) (k : ℕ) (hk : 1 ≤ k) (x : S) :
    (m.T)^[k] m.Jbar x = ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  simp [Model.T]

/-- Pointwise: the closure-in-λ of the projection equals the epigraph of the infimum. -/
theorem aux_l2p_pbar_pt {C : Type*} (U : Set C) (h : C → EReal) (l : ℝ) :
    (∃ lam : ℕ → ℝ, Tendsto lam atTop (𝓝 l) ∧ ∀ n, ∃ u ∈ U, h u ≤ (lam n : EReal)) ↔
      (⨅ v ∈ U, h v) ≤ (l : EReal) := by
  constructor
  · rintro ⟨lam, hlam, hmem⟩
    have h1 : ∀ n, (⨅ v ∈ U, h v) ≤ ((lam n : ℝ) : EReal) := by
      intro n
      obtain ⟨u, hu, hle⟩ := hmem n
      exact le_trans (iInf₂_le u hu) hle
    have h2 : Tendsto (fun n => ((lam n : ℝ) : EReal)) atTop (𝓝 (l : EReal)) :=
      (continuous_coe_real_ereal.tendsto l).comp hlam
    exact ge_of_tendsto' h2 h1
  · intro hle
    refine ⟨fun n => l + 1 / ((n : ℝ) + 1), ?_, ?_⟩
    · have := (tendsto_const_nhds (x := l)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    · intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hlt : (⨅ v ∈ U, h v) < ((l + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
        refine lt_of_le_of_lt hle ?_
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      obtain ⟨u, hu⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hU, hu2⟩ := iInf_lt_iff.mp hu
      exact ⟨u, hU, hu2.le⟩

theorem aux_l2p_pbar_eq {S C : Type*} (m : Model S C) (k : ℕ) (hk : 1 ≤ k) :
    Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar) := by
  ext ⟨x, l⟩
  simp only [Pbar, E, Model.P, Model.Ck, Set.mem_ofPred_eq]
  rw [aux_l2p_iter m k hk x]
  have := aux_l2p_pbar_pt (m.U x) (fun u => m.H x u ((m.T)^[k - 1] m.Jbar)) l
  rw [← this]
  constructor
  · rintro ⟨lam, hlam, hmem⟩
    exact ⟨lam, hlam, fun n => by
      obtain ⟨u, hu, _, h2⟩ := hmem n
      exact ⟨u, hu, h2⟩⟩
  · rintro ⟨lam, hlam, hmem⟩
    exact ⟨lam, hlam, fun n => by
      obtain ⟨u, hu, h2⟩ := hmem n
      exact ⟨u, hu, hu, h2⟩⟩

/-- Under Assumption I, `J̄ ≤ T^k(J̄)`. -/
theorem aux_l2p_ge {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    ∀ k : ℕ, m.Jbar ≤ (m.T)^[k] m.Jbar := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ j ih =>
    intro x
    rw [Function.iterate_succ_apply']
    simp only [Model.T]
    refine le_iInf₂ fun u hu => ?_
    exact le_trans (hI x u hu) (m.mono x u hu _ _ ih)

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem MonotoneDP.Increase.lemma2_projection_epigraph {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    ∀ k : ℕ, 1 ≤ k →
      (m.P (m.Ck k) ⊆ Pbar (m.P (m.Ck k)) ∧
        Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ∧
      ((m.P (m.Ck k) = Pbar (m.P (m.Ck k)) ∧
          Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ↔
        ∀ x : S, ∃ u ∈ m.U x,
          m.H x u ((m.T)^[k - 1] m.Jbar) =
            ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar)) := by
  intro k hk
  have hPE := aux_l2p_pbar_eq m k hk
  have hsub : m.P (m.Ck k) ⊆ Pbar (m.P (m.Ck k)) := by
    rintro ⟨x, l⟩ hp
    exact ⟨fun _ => l, tendsto_const_nhds, fun _ => hp⟩
  refine ⟨⟨hsub, hPE⟩, ?_⟩
  rw [hPE]
  constructor
  · rintro ⟨hPeq, -⟩ x
    set t : EReal := ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar) with ht
    have htk : (m.T)^[k] m.Jbar x = t := aux_l2p_iter m k hk x
    suffices hex : ∃ u ∈ m.U x, m.H x u ((m.T)^[k - 1] m.Jbar) ≤ t by
      obtain ⟨u, hu, hle⟩ := hex
      exact ⟨u, hu, le_antisymm hle (iInf₂_le u hu)⟩
    by_cases htop : t = ⊤
    · obtain ⟨u, hu⟩ := m.U_nonempty x
      exact ⟨u, hu, by rw [htop]; exact le_top⟩
    · have hbot : t ≠ ⊥ := by
        intro hb
        have h1 := aux_l2p_ge m hI k x
        rw [htk, hb, le_bot_iff] at h1
        exact m.Jbar_ne_bot x h1
      have hcoe : ((t.toReal : ℝ) : EReal) = t := EReal.coe_toReal htop hbot
      have hmemE : (x, t.toReal) ∈ E ((m.T)^[k] m.Jbar) := by
        simp only [E, Set.mem_ofPred_eq]
        rw [htk, hcoe]
      rw [← hPeq] at hmemE
      obtain ⟨u, hu, hC⟩ := hmemE
      refine ⟨u, hu, ?_⟩
      have := hC.2
      simp only at this
      rwa [hcoe] at this
  · intro hatt
    refine ⟨?_, rfl⟩
    apply Set.Subset.antisymm
    · rw [← hPE]; exact hsub
    · rintro ⟨x, l⟩ hp
      simp only [E, Set.mem_ofPred_eq] at hp
      rw [aux_l2p_iter m k hk x] at hp
      obtain ⟨u, hu, heq⟩ := hatt x
      refine ⟨u, hu, hu, ?_⟩
      simp only
      rw [heq]
      exact hp

end
-- END MODULE AttributedEpigraph

-- BEGIN MODULE AttributedStationaryBellman
section
-- Prove2me | solution 1 for MonotoneDP.Increase.cor5_1_stationary_bellman
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:53:00.806831+00:00
-- url     : https://prove2.me/submissions/1cd3fc1d-7ea5-476c-9e1b-dad631df8bf5


namespace MonotoneDP.Increase

open Filter Topology

theorem aux_c51_comp_eq {S C : Type*} (m : Model S C) (μ : m.Selector) :
    ∀ (N : ℕ) (J : S → EReal), m.comp (m.stationary μ) N J = (m.Tmu μ)^[N] J := by
  intro N
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp (m.stationary μ) N (m.Tmu μ J) = _
    rw [ih, Function.iterate_succ_apply]

theorem aux_c51_mono {S C : Type*} (m : Model S C) (μ : m.Selector) :
    Monotone (m.Tmu μ) := by
  intro J J' h x
  exact m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_c51_seq_mono {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (μ : m.Selector) :
    Monotone (fun n => (m.Tmu μ)^[n] m.Jbar) := by
  apply Monotone.monotone_iterate_of_le_map (aux_c51_mono m μ)
  intro x
  exact hI x (μ.1 x) (μ.2 x)

theorem aux_c51_Jmu_eq {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (μ : m.Selector)
    (x : S) : m.Jmu μ x = ⨆ n, (m.Tmu μ)^[n] m.Jbar x := by
  unfold Model.Jmu Model.Jpi
  simp only [aux_c51_comp_eq]
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_c51_seq_mono m hI μ hab x

end MonotoneDP.Increase

open MonotoneDP.Increase
open Filter Topology

theorem MonotoneDP.Increase.cor5_1_stationary_bellman {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (_hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ μ : m.Selector, m.Jmu μ = m.Tmu μ (m.Jmu μ) ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.Tmu μ J' ≤ J' → m.Jmu μ ≤ J' := by
  intro μ
  have hseq := aux_c51_seq_mono m hI μ
  have hJ : ∀ x, m.Jmu μ x = ⨆ n, (m.Tmu μ)^[n] m.Jbar x := aux_c51_Jmu_eq m hI μ
  refine ⟨?_, ?_⟩
  · funext x
    have hge : ∀ k, m.Jbar ≤ (m.Tmu μ)^[k] m.Jbar := fun k => hseq (Nat.zero_le k)
    have h1 := hI1 (fun k => (m.Tmu μ)^[k] m.Jbar) hge (fun k => hseq (Nat.le_succ k))
      x (μ.1 x) (μ.2 x)
    have hlim : (fun y => limUnder atTop (fun k => (m.Tmu μ)^[k] m.Jbar y)) = m.Jmu μ := by
      funext y
      rw [hJ y]
      apply Tendsto.limUnder_eq
      apply tendsto_atTop_iSup
      intro a b hab
      exact hseq hab y
    rw [hlim] at h1
    show m.Jmu μ x = m.H x (μ.1 x) (m.Jmu μ)
    rw [← h1]
    have hshift : (fun k => m.H x (μ.1 x) ((m.Tmu μ)^[k] m.Jbar)) =
        fun k => (m.Tmu μ)^[k+1] m.Jbar x := by
      funext k
      rw [Function.iterate_succ_apply']
      rfl
    rw [hshift]
    symm
    apply Tendsto.limUnder_eq
    have ht : Tendsto (fun k => (m.Tmu μ)^[k] m.Jbar x) atTop (𝓝 (m.Jmu μ x)) := by
      rw [hJ x]
      apply tendsto_atTop_iSup
      intro a b hab
      exact hseq hab x
    exact ht.comp (tendsto_add_atTop_nat 1)
  · intro J' hJ' hT
    have hle : ∀ n, (m.Tmu μ)^[n] m.Jbar ≤ J' := by
      intro n
      induction n with
      | zero => exact hJ'
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact le_trans (aux_c51_mono m μ ih) hT
    intro x
    rw [hJ x]
    exact iSup_le fun n => hle n x

end
-- END MODULE AttributedStationaryBellman

-- BEGIN MODULE AttributedBellman
section
-- Prove2me | solution 1 for MonotoneDP.Increase.prop5_bellman_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:10:00.046557+00:00
-- url     : https://prove2.me/submissions/bd3e13e0-724a-4cb2-bcd7-137e7c683efa


namespace MonotoneDP.Increase

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

theorem aux_p5_Tmu_mono (μ : m.Selector) {J J' : S → EReal} (h : J ≤ J') :
    m.Tmu μ J ≤ m.Tmu μ J' := fun x => m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_p5_T_mono {J J' : S → EReal} (h : J ≤ J') : m.T J ≤ m.T J' := by
  intro x
  exact iInf₂_mono fun u hu => m.mono x u hu J J' h

theorem aux_p5_comp_mono (π : m.Policy) (N : ℕ) : ∀ {J J' : S → EReal}, J ≤ J' →
    m.comp π N J ≤ m.comp π N J' := by
  induction N with
  | zero => intro J J' h; exact h
  | succ N ih => intro J J' h; exact ih (m.aux_p5_Tmu_mono (π N) h)

theorem aux_p5_comp_succ (π : m.Policy) (N : ℕ) : ∀ J : S → EReal,
    m.comp π (N+1) J = m.Tmu (π 0) (m.comp (fun k => π (k+1)) N J) := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N+1) (m.Tmu (π (N+1)) J) = _
    rw [ih]
    rfl

theorem aux_p5_comp_le_succ (hI : m.AssumptionI) (π : m.Policy) (N : ℕ) :
    m.comp π N m.Jbar ≤ m.comp π (N+1) m.Jbar := by
  show m.comp π N m.Jbar ≤ m.comp π N (m.Tmu (π N) m.Jbar)
  apply m.aux_p5_comp_mono
  intro x
  exact hI x _ ((π N).2 x)

theorem aux_p5_comp_monotone (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Monotone (fun N => m.comp π N m.Jbar x) :=
  monotone_nat_of_le_succ fun N => m.aux_p5_comp_le_succ hI π N x

theorem aux_p5_Jpi_eq (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨆ N, m.comp π N m.Jbar x :=
  (tendsto_atTop_iSup (m.aux_p5_comp_monotone hI π x)).limUnder_eq

theorem aux_p5_Jbar_le_Jpi (hI : m.AssumptionI) (π : m.Policy) : m.Jbar ≤ m.Jpi π := by
  intro x
  rw [m.aux_p5_Jpi_eq hI π x]
  exact le_iSup (fun N => m.comp π N m.Jbar x) 0

theorem aux_p5_Jbar_le_Jstar (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  exact le_iInf fun π => m.aux_p5_Jbar_le_Jpi hI π x

theorem aux_p5_Jpi_shift (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (π : m.Policy) (x : S) :
    m.Jpi π x = m.H x ((π 0).1 x) (m.Jpi (fun k => π (k+1))) := by
  set π' : m.Policy := fun k => π (k+1) with hπ'
  have h1 := hI1 (fun k => m.comp π' k m.Jbar)
    (fun k y => m.aux_p5_comp_monotone hI π' y (Nat.zero_le k))
    (fun k => m.aux_p5_comp_le_succ hI π' k) x ((π 0).1 x) ((π 0).2 x)
  have h2 : (fun y => limUnder atTop (fun k => m.comp π' k m.Jbar y)) = m.Jpi π' := rfl
  rw [h2] at h1
  rw [← h1]
  have ht : Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (⨆ N, m.comp π N m.Jbar x)) :=
    tendsto_atTop_iSup (m.aux_p5_comp_monotone hI π x)
  have ht' : Tendsto (fun k => m.H x ((π 0).1 x) (m.comp π' k m.Jbar)) atTop
      (𝓝 (⨆ N, m.comp π N m.Jbar x)) := by
    have := ht.comp (tendsto_add_atTop_nat 1)
    refine this.congr ?_
    intro k
    simp only [Function.comp]
    rw [m.aux_p5_comp_succ π k]
    rfl
  rw [ht'.limUnder_eq, m.aux_p5_Jpi_eq hI π x]

theorem aux_p5_T_Jstar_le (hI : m.AssumptionI) (hI1 : m.AssumptionI1) :
    m.T m.Jstar ≤ m.Jstar := by
  intro x
  refine le_iInf fun π => ?_
  rw [m.aux_p5_Jpi_shift hI hI1 π x]
  calc m.T m.Jstar x ≤ m.H x ((π 0).1 x) m.Jstar :=
        iInf₂_le (f := fun u _ => m.H x u m.Jstar) _ ((π 0).2 x)
    _ ≤ _ := m.mono x _ ((π 0).2 x) _ _ (fun y => iInf_le (fun π => m.Jpi π y) _)

theorem aux_p5_selector (J' : S → EReal) (hJ' : m.Jbar ≤ J') (hT : m.T J' ≤ J') (δ : ℝ)
    (hδ : 0 < δ) : ∃ μ : m.Selector, ∀ x, m.H x (μ.1 x) J' ≤ J' x + (δ : EReal) := by
  have h : ∀ x, ∃ u ∈ m.U x, m.H x u J' ≤ J' x + (δ : EReal) := by
    intro x
    by_cases htop : J' x = ⊤
    · obtain ⟨u, hu⟩ := m.U_nonempty x
      refine ⟨u, hu, ?_⟩
      rw [htop, EReal.top_add_coe]
      exact le_top
    · have hbot : J' x ≠ ⊥ := by
        intro hb
        have := hJ' x
        rw [hb, le_bot_iff] at this
        exact m.Jbar_ne_bot x this
      have hlt : J' x < J' x + (δ : EReal) := by
        obtain ⟨a, ha⟩ : ∃ a : ℝ, J' x = a := ⟨(J' x).toReal, (EReal.coe_toReal htop hbot).symm⟩
        rw [ha, ← EReal.coe_add]
        exact_mod_cast (by linarith : a < a + δ)
      have hlt2 : m.T J' x < J' x + δ := lt_of_le_of_lt (hT x) hlt
      simp only [T, iInf_lt_iff] at hlt2
      obtain ⟨u, hu, hlt'⟩ := hlt2
      exact ⟨u, hu, hlt'.le⟩
  choose f hf using h
  exact ⟨⟨f, fun x => (hf x).1⟩, fun x => (hf x).2⟩

theorem aux_p5_min (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) (J' : S → EReal)
    (hJ' : m.Jbar ≤ J') (hT : m.T J' ≤ J') : m.Jstar ≤ J' := by
  obtain ⟨α, hα, hI2⟩ := hI2
  have key : ∀ ε : ℝ, 0 < ε → m.Jstar ≤ fun y => J' y + (ε : EReal) := by
    intro ε hε
    set c : ℕ → ℝ := fun N => ε / (2 * α) ^ N with hcdef
    have hc : ∀ N, 0 < c N := fun N => by
      simp only [hcdef]
      positivity
    have hrec : ∀ N, c N / 2 + α * c (N+1) = c N := by
      intro N
      simp only [hcdef]
      rw [pow_succ]
      field_simp
      ring
    choose μ hμ using fun N => m.aux_p5_selector J' hJ' hT (c N / 2) (by linarith [hc N])
    let π : m.Policy := μ
    have claim : ∀ N, ∀ J : S → EReal, J ≤ (fun y => J' y + (c N : EReal)) →
        m.comp π N J ≤ fun y => J' y + (c 0 : EReal) := by
      intro N
      induction N with
      | zero => intro J h; exact h
      | succ N ih =>
        intro J h
        apply ih
        intro y
        calc m.Tmu (π N) J y = m.H y ((μ N).1 y) J := rfl
          _ ≤ m.H y ((μ N).1 y) (fun z => J' z + (c (N+1) : EReal)) :=
              m.mono y _ ((μ N).2 y) _ _ h
          _ ≤ m.H y ((μ N).1 y) J' + ((α * c (N+1) : ℝ) : EReal) :=
              (hI2 (c (N+1)) (hc _) J' hJ' y _ ((μ N).2 y)).2
          _ ≤ (J' y + ((c N / 2 : ℝ) : EReal)) + ((α * c (N+1) : ℝ) : EReal) := by
              gcongr
              exact hμ N y
          _ = J' y + ((c N / 2 + α * c (N+1) : ℝ) : EReal) := by
              rw [add_assoc, EReal.coe_add]
          _ = J' y + (c N : EReal) := by rw [hrec N]
    intro x
    have hc0 : c 0 = ε := by simp [hcdef]
    calc m.Jstar x ≤ m.Jpi π x := iInf_le (fun π => m.Jpi π x) π
      _ = ⨆ N, m.comp π N m.Jbar x := m.aux_p5_Jpi_eq hI π x
      _ ≤ J' x + (ε : EReal) := by
          refine iSup_le fun N => ?_
          have h1 : m.comp π N m.Jbar x ≤ m.comp π N J' x := m.aux_p5_comp_mono π N hJ' x
          have h2 : m.comp π N J' x ≤ J' x + (c 0 : EReal) := by
            refine claim N J' ?_ x
            intro y
            exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (hc N).le)
          rw [hc0] at h2
          exact h1.trans h2
  intro x
  by_cases htop : J' x = ⊤
  · rw [htop]; exact le_top
  have hbot : J' x ≠ ⊥ := by
    intro hb
    have := hJ' x
    rw [hb, le_bot_iff] at this
    exact m.Jbar_ne_bot x this
  obtain ⟨a, ha⟩ : ∃ a : ℝ, J' x = a := ⟨(J' x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [ha]
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  have hz' : a < z := by exact_mod_cast hz
  have := key (z - a) (by linarith) x
  simp only at this
  rw [ha, ← EReal.coe_add] at this
  simpa using this

end Model

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem MonotoneDP.Increase.prop5_bellman_equation {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.T J' ≤ J' → m.Jstar ≤ J' := by
  refine ⟨?_, fun J' hJ' hT => m.aux_p5_min hI hI2 J' hJ' hT⟩
  refine le_antisymm ?_ (m.aux_p5_T_Jstar_le hI hI1)
  apply m.aux_p5_min hI hI2
  · intro x
    refine le_iInf₂ fun u hu => ?_
    exact (hI x u hu).trans (m.mono x u hu _ _ (m.aux_p5_Jbar_le_Jstar hI))
  · exact m.aux_p5_T_mono (m.aux_p5_T_Jstar_le hI hI1)

end
-- END MODULE AttributedBellman

-- BEGIN MODULE AttributedCompactConvergence
section
-- Prove2me | solution 1 for MonotoneDP.Increase.prop12_compactness_convergence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:40:37.415314+00:00
-- url     : https://prove2.me/submissions/da0de76b-a1a4-433d-8793-68d928cd480b

open MonotoneDP.Increase Filter Topology
namespace CIncrease_prop12_compactness_convergence

theorem comp_mono {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => exact monotone_id
  | succ N ih =>
    intro J K hJK
    apply ih
    exact fun x => m.mono x _ ((π N).2 x) J K hJK

theorem comp_monotone {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) :
    Monotone (fun N => m.comp π N m.Jbar) := by
  apply monotone_nat_of_le_succ
  intro N
  exact comp_mono m π N (fun x => hI x _ ((π N).2 x))

theorem Jpi_eq_iSup {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x=⨆ N, m.comp π N m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem policy_tendsto {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (m.Jpi π x)) := by
  rw [Jpi_eq_iSup m hI]
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem Jbar_le_Jstar {S C : Type*} (m : Model S C) (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  apply le_iInf
  intro π
  rw [Jpi_eq_iSup m hI]
  exact le_iSup_of_le 0 le_rfl

theorem T_le_Tmu {S C : Type*} (m : Model S C) (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J :=
  fun x => iInf_le_of_le (μ.1 x) (iInf_le_of_le (μ.2 x) le_rfl)

theorem comp_head {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp π (N+1) J=m.Tmu (π 0) (m.comp (fun k => π (k+1)) N J) := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih => exact ih (m.Tmu (π (N+1)) J)

theorem Jpi_head {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (hI1 : m.AssumptionI1)
    (π : m.Policy) : m.Jpi π=m.Tmu (π 0) (m.Jpi (fun k => π (k+1))) := by
  funext x
  have h := hI1 (fun N => m.comp (fun k => π (k+1)) N m.Jbar)
    (fun N => comp_monotone m hI _ (Nat.zero_le N))
    (fun N => comp_monotone m hI _ (Nat.le_succ N)) x _ ((π 0).2 x)
  have hl : limUnder atTop (fun N => m.H x ((π 0).1 x) (m.comp (fun k => π (k+1)) N m.Jbar))=m.Jpi π x := by
    apply Tendsto.limUnder_eq
    change Tendsto (fun N => m.Tmu (π 0) (m.comp (fun k => π (k+1)) N m.Jbar) x) atTop (𝓝 (m.Jpi π x))
    simp_rw [← comp_head]
    exact (tendsto_add_atTop_iff_nat 1).mpr (policy_tendsto m hI π x)
  exact hl.symm.trans h
end CIncrease_prop12_compactness_convergence

private theorem criterion {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar) ∧
      ((∃ π : m.Policy, m.Jpi π=m.Jstar) → ∃ μ : m.Selector, m.Jmu μ=m.Jstar) := by
  have hb := (prop5_bellman_equation m hI hI1 hI2).1
  have hcriterion : ∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar := by
    intro μ
    have hμ := cor5_1_stationary_bellman m hI hI1 hI2 μ
    constructor
    · intro h
      rw [h] at hμ
      exact hμ.1.symm.trans hb
    · intro h
      apply le_antisymm
      · exact hμ.2 m.Jstar (CIncrease_prop12_compactness_convergence.Jbar_le_Jstar m hI) (by rw [h,← hb])
      · exact fun x => iInf_le (fun π : m.Policy => m.Jpi π x) (m.stationary μ)
  refine ⟨hcriterion,?_⟩
  rintro ⟨π,hπ⟩
  refine ⟨π 0,(hcriterion (π 0)).mpr ?_⟩
  apply le_antisymm
  · rw [← hb,← hπ]
    have hh := CIncrease_prop12_compactness_convergence.Jpi_head m hI hI1 π
    conv_rhs => rw [hh]
    intro x
    apply m.mono x _ ((π 0).2 x)
    intro y
    rw [hπ]
    exact iInf_le _ _
  · exact CIncrease_prop12_compactness_convergence.T_le_Tmu m (π 0) m.Jstar

namespace CIncrease_prop12_compactness_convergence

theorem T_mono {S C : Type*} (m : Model S C) : Monotone m.T := by
  intro J K h x
  exact iInf_mono (fun u => iInf_mono (fun hu => m.mono x u hu J K h))

theorem iterate_monotone {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    Monotone (fun k => m.T^[k] m.Jbar) :=
  (T_mono m).monotone_iterate_of_le_map (fun x => le_iInf (fun u => le_iInf (fun hu => hI x u hu)))

theorem Jinf_eq_iSup {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (x : S) :
    m.Jinf x=⨆ k, m.T^[k] m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iSup (fun i j hij => iterate_monotone m hI hij x)

theorem Jbar_le_Jinf {S C : Type*} (m : Model S C) (hI : m.AssumptionI) : m.Jbar ≤ m.Jinf := by
  intro x
  rw [Jinf_eq_iSup m hI]
  exact le_iSup_of_le 0 le_rfl

theorem E_injective {S : Type*} : Function.Injective (E : (S → EReal) → Set (S × ℝ)) := by
  intro J K h
  funext x
  apply le_antisymm
  all_goals
    by_contra hn
    obtain ⟨r,hr1,hr2⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  · have hm : (x,r)∈E K := hr1.le
    rw [← h] at hm
    exact (not_le_of_gt hr2) hm
  · have hm : (x,r)∈E J := hr1.le
    rw [h] at hm
    exact (not_le_of_gt hr2) hm

theorem projected_intersection {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) :
    m.P (⋂ k ≥ 1, m.Ck k)={p : S × ℝ | ∃ u∈m.U p.1, m.H p.1 u m.Jinf ≤ (p.2 : EReal)} := by
  have hh : ∀ x u, u∈m.U x → m.H x u m.Jinf=⨆ k, m.H x u (m.T^[k] m.Jbar) := by
    intro x u hu
    have he := hI1 (fun k => m.T^[k] m.Jbar)
      (fun k => iterate_monotone m hI (Nat.zero_le k))
      (fun k => iterate_monotone m hI (Nat.le_succ k)) x u hu
    have ht := tendsto_atTop_iSup (fun i j hij => m.mono x u hu _ _ (iterate_monotone m hI hij))
    exact he.symm.trans ht.limUnder_eq
  ext p
  constructor
  · rintro ⟨u,hu,hall⟩
    refine ⟨u,hu,?_⟩
    rw [hh _ _ hu]
    apply iSup_le
    intro k
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hall (k+1)) (by omega : 1 ≤ k+1)
    simpa [Model.Ck] using h.2
  · rintro ⟨u,hu,h⟩
    refine ⟨u,hu,Set.mem_iInter.mpr (fun k => Set.mem_iInter.mpr (fun hk => ?_))⟩
    refine ⟨hu,?_⟩
    exact (le_iSup (fun k => m.H p.1 u (m.T^[k] m.Jbar)) (k-1)).trans (by rwa [← hh _ _ hu])

theorem closed_projected_intersection {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    (⋂ k ≥ 1, Pbar (m.P (m.Ck k)))=E m.Jinf := by
  ext p
  simp only [Set.mem_iInter,E,Set.mem_ofPred_eq]
  constructor
  · intro h
    rw [Jinf_eq_iSup m hI]
    apply iSup_le
    intro k
    have hh := h (k+1) (by omega)
    rw [(lemma2_projection_epigraph m hI (k+1) (by omega)).1.2] at hh
    exact (iterate_monotone m hI (Nat.le_succ k) p.1).trans hh
  · intro h k hk
    rw [(lemma2_projection_epigraph m hI k hk).1.2]
    change m.T^[k] m.Jbar p.1 ≤ (p.2 : EReal)
    exact (le_iSup (fun k => m.T^[k] m.Jbar p.1) k).trans (by rwa [← Jinf_eq_iSup m hI])
end CIncrease_prop12_compactness_convergence

private theorem characterization {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ((m.Jinf=m.T m.Jinf ↔
        Pbar (m.P (⋂ k ≥ 1, m.Ck k))=⋂ k ≥ 1, Pbar (m.P (m.Ck k))) ∧
      (m.Jinf=m.Jstar ↔
        Pbar (m.P (⋂ k ≥ 1, m.Ck k))=⋂ k ≥ 1, Pbar (m.P (m.Ck k)))) ∧
    (((m.Jinf=m.T m.Jinf ∧
          ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) ↔
        m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k))) ∧
      ((m.Jinf=m.Jstar ∧ ∃ μ : m.Selector, m.Jmu μ=m.Jstar) ↔
        m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k)))) := by
  classical
  have h10 := prop10_dp_limit_le_optimal m hI hI1 hI2
  let m' : Model S C := {m with
    Jbar := m.Jinf
    Jbar_ne_bot := fun x => ne_bot_of_le_ne_bot (m.Jbar_ne_bot x) (CIncrease_prop12_compactness_convergence.Jbar_le_Jinf m hI x) }
  have hI' : m'.AssumptionI := by
    intro x u hu
    exact (h10.1.1 x).trans (iInf_le_of_le u (iInf_le_of_le hu le_rfl))
  have hp : m'.P (m'.Ck 1)=m.P (⋂ k ≥ 1, m.Ck k) := by
    rw [CIncrease_prop12_compactness_convergence.projected_intersection m hI hI1]
    ext p
    simp [Model.P,Model.Ck,m']
  have hepi := lemma2_projection_epigraph m' hI' 1 le_rfl
  rw [hp] at hepi
  change
    (m.P (⋂ k ≥ 1, m.Ck k) ⊆ Pbar (m.P (⋂ k ≥ 1, m.Ck k)) ∧
      Pbar (m.P (⋂ k ≥ 1, m.Ck k))=E (m.T m.Jinf)) ∧
    ((m.P (⋂ k ≥ 1, m.Ck k)=Pbar (m.P (⋂ k ≥ 1, m.Ck k)) ∧
      Pbar (m.P (⋂ k ≥ 1, m.Ck k))=E (m.T m.Jinf)) ↔
      ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) at hepi
  have hstar : m.Jinf=m.Jstar ↔ m.Jinf=m.T m.Jinf := by
    constructor
    · intro h
      rw [h,h10.1.2.2]
    · intro h
      have hh := h10.2.mpr h
      exact hh.1.trans (hh.2.1.trans hh.2.2)
  have hfix : m.Jinf=m.T m.Jinf ↔ Pbar (m.P (⋂ k ≥ 1, m.Ck k))=E m.Jinf := by
    rw [hepi.1.2]
    exact ⟨fun h => congrArg E h.symm,fun h => (CIncrease_prop12_compactness_convergence.E_injective h).symm⟩
  have hatt : (m.Jinf=m.T m.Jinf ∧
      ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) ↔
      m.P (⋂ k ≥ 1, m.Ck k)=E m.Jinf := by
    constructor
    · rintro ⟨hf,ha⟩
      exact (hepi.2.mpr ha).1.trans (hfix.mp hf)
    · intro hpE
      have hf : m.Jinf=m.T m.Jinf := by
        apply hfix.mpr
        apply Set.Subset.antisymm
        · rw [hepi.1.2]
          exact fun p h => (h10.1.1 p.1).trans h
        · rw [← hpE]
          exact hepi.1.1
      refine ⟨hf,hepi.2.mp ⟨?_,hepi.1.2⟩⟩
      exact hpE.trans (hfix.mp hf).symm
  have hopt : (m.Jinf=m.Jstar ∧ ∃ μ : m.Selector, m.Jmu μ=m.Jstar) ↔
      (m.Jinf=m.T m.Jinf ∧ ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) := by
    constructor
    · rintro ⟨hj,μ,hμ⟩
      refine ⟨hstar.mp hj,?_⟩
      intro x
      refine ⟨μ.1 x,μ.2 x,?_⟩
      rw [hj]
      exact congrFun ((criterion m hI hI1 hI2).1 μ |>.mp hμ) x
    · rintro ⟨hf,ha⟩
      have hj := hstar.mpr hf
      choose u hu he using ha
      let μ : m.Selector := ⟨u,hu⟩
      refine ⟨hj,μ,(criterion m hI hI1 hI2).1 μ |>.mpr ?_⟩
      rw [← hj]
      funext x
      exact he x
  rw [CIncrease_prop12_compactness_convergence.closed_projected_intersection m hI]
  exact ⟨⟨hfix,hstar.trans hfix⟩,⟨hatt,hopt.trans hatt⟩⟩

theorem MonotoneDP.Increase.prop12_compactness_convergence {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α)
    (hcpt : ∃ kbar : ℕ, ∀ x : S, ∀ lam : ℝ, ∀ k : ℕ, kbar ≤ k →
      IsCompact {u | u∈m.U x ∧ m.H x u ((m.T)^[k] m.Jbar) ≤ (lam : EReal)}) :
    m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k)) ∧
      (m.Jinf=m.T m.Jinf ∧ m.T m.Jinf=m.T m.Jstar ∧ m.T m.Jstar=m.Jstar) ∧
      ∃ μ : m.Selector, m.Jmu μ=m.Jstar := by
  classical
  obtain ⟨kbar,hcpt⟩ := hcpt
  have hp : m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k)) := by
    apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨u,hu,hh⟩ := hp
      apply Set.mem_iInter.mpr
      intro k
      apply Set.mem_iInter.mpr
      intro hk
      exact (lemma2_projection_epigraph m hI k hk).1.1
        ⟨u,hu,Set.mem_iInter.mp (Set.mem_iInter.mp hh k) hk⟩
    · intro p hp
      have hv : ∀ k, 1 ≤ k → (m.T^[k] m.Jbar) p.1 ≤ (p.2 : EReal) := by
        intro k hk
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp hp k) hk
        rw [(lemma2_projection_epigraph m hI k hk).1.2] at hh
        exact hh
      let K : ℕ → Set C := fun j => {u | u∈m.U p.1 ∧ m.H p.1 u (m.T^[j+kbar] m.Jbar) ≤ (p.2 : EReal)}
      have hK : ∀ j, IsCompact (K j) := fun j => hcpt p.1 p.2 (j+kbar) (by omega)
      have hnon : ∀ j, (K j).Nonempty := by
        intro j
        obtain ⟨u,hu,hmin⟩ := lemma3_compact_sublevel_min
          (fun u => m.H p.1 u (m.T^[j+kbar] m.Jbar)) (m.U p.1) (m.U_nonempty p.1)
          (fun r => hcpt p.1 r (j+kbar) (by omega))
        refine ⟨u,hu,?_⟩
        have hle : m.H p.1 u (m.T^[j+kbar] m.Jbar) ≤ m.T (m.T^[j+kbar] m.Jbar) p.1 := by
          exact le_iInf (fun v => le_iInf (fun hv => hmin hv))
        exact hle.trans (by simpa only [Function.iterate_succ_apply'] using hv (j+kbar+1) (by omega))
      have hdec : ∀ j, K (j+1) ⊆ K j := by
        intro j u hu
        refine ⟨hu.1,?_⟩
        exact (m.mono p.1 u hu.1 _ _ (CIncrease_prop12_compactness_convergence.iterate_monotone m hI (by omega : j+kbar ≤ j+1+kbar))).trans hu.2
      obtain ⟨u,hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hdec hnon (hK 0) (fun j => (hK j).isClosed)
      have huj := fun j => Set.mem_iInter.mp hu j
      refine ⟨u,(huj 0).1,Set.mem_iInter.mpr (fun k => Set.mem_iInter.mpr (fun hk => ?_))⟩
      refine ⟨(huj 0).1,?_⟩
      exact (m.mono p.1 u (huj 0).1 _ _ (CIncrease_prop12_compactness_convergence.iterate_monotone m hI (by omega : k-1 ≤ k+kbar))).trans (huj k).2
  have hh := characterization m hI hI1 hI2
  exact ⟨hp,(prop10_dp_limit_le_optimal m hI hI1 hI2).2.mpr (hh.2.1.mpr hp).1,(hh.2.2.mpr hp).2⟩

end
-- END MODULE AttributedCompactConvergence

-- BEGIN MODULE AttributedStationaryCriterion
section
-- Prove2me | solution 1 for MonotoneDP.Increase.prop7_optimal_stationary_criterion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:32:46.129867+00:00
-- url     : https://prove2.me/submissions/f8bcb553-bd54-4eb9-90a4-9e436dde819e

open MonotoneDP.Increase Filter Topology
namespace CIncrease_prop7_optimal_stationary_criterion

theorem comp_mono {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => exact monotone_id
  | succ N ih =>
    intro J K hJK
    apply ih
    exact fun x => m.mono x _ ((π N).2 x) J K hJK

theorem comp_monotone {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) :
    Monotone (fun N => m.comp π N m.Jbar) := by
  apply monotone_nat_of_le_succ
  intro N
  exact comp_mono m π N (fun x => hI x _ ((π N).2 x))

theorem Jpi_eq_iSup {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x=⨆ N, m.comp π N m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem policy_tendsto {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (m.Jpi π x)) := by
  rw [Jpi_eq_iSup m hI]
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem Jbar_le_Jstar {S C : Type*} (m : Model S C) (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  apply le_iInf
  intro π
  rw [Jpi_eq_iSup m hI]
  exact le_iSup_of_le 0 le_rfl

theorem T_le_Tmu {S C : Type*} (m : Model S C) (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J :=
  fun x => iInf_le_of_le (μ.1 x) (iInf_le_of_le (μ.2 x) le_rfl)

theorem comp_head {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp π (N+1) J=m.Tmu (π 0) (m.comp (fun k => π (k+1)) N J) := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih => exact ih (m.Tmu (π (N+1)) J)

theorem Jpi_head {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (hI1 : m.AssumptionI1)
    (π : m.Policy) : m.Jpi π=m.Tmu (π 0) (m.Jpi (fun k => π (k+1))) := by
  funext x
  have h := hI1 (fun N => m.comp (fun k => π (k+1)) N m.Jbar)
    (fun N => comp_monotone m hI _ (Nat.zero_le N))
    (fun N => comp_monotone m hI _ (Nat.le_succ N)) x _ ((π 0).2 x)
  have hl : limUnder atTop (fun N => m.H x ((π 0).1 x) (m.comp (fun k => π (k+1)) N m.Jbar))=m.Jpi π x := by
    apply Tendsto.limUnder_eq
    change Tendsto (fun N => m.Tmu (π 0) (m.comp (fun k => π (k+1)) N m.Jbar) x) atTop (𝓝 (m.Jpi π x))
    simp_rw [← comp_head]
    exact (tendsto_add_atTop_iff_nat 1).mpr (policy_tendsto m hI π x)
  exact hl.symm.trans h
end CIncrease_prop7_optimal_stationary_criterion

theorem MonotoneDP.Increase.prop7_optimal_stationary_criterion {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar) ∧
      ((∃ π : m.Policy, m.Jpi π=m.Jstar) → ∃ μ : m.Selector, m.Jmu μ=m.Jstar) := by
  have hb := (prop5_bellman_equation m hI hI1 hI2).1
  have hcriterion : ∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar := by
    intro μ
    have hμ := cor5_1_stationary_bellman m hI hI1 hI2 μ
    constructor
    · intro h
      rw [h] at hμ
      exact hμ.1.symm.trans hb
    · intro h
      apply le_antisymm
      · exact hμ.2 m.Jstar (CIncrease_prop7_optimal_stationary_criterion.Jbar_le_Jstar m hI) (by rw [h,← hb])
      · exact fun x => iInf_le (fun π : m.Policy => m.Jpi π x) (m.stationary μ)
  refine ⟨hcriterion,?_⟩
  rintro ⟨π,hπ⟩
  refine ⟨π 0,(hcriterion (π 0)).mpr ?_⟩
  apply le_antisymm
  · rw [← hb,← hπ]
    have hh := CIncrease_prop7_optimal_stationary_criterion.Jpi_head m hI hI1 π
    conv_rhs => rw [hh]
    intro x
    apply m.mono x _ ((π 0).2 x)
    intro y
    rw [hπ]
    exact iInf_le _ _
  · exact CIncrease_prop7_optimal_stationary_criterion.T_le_Tmu m (π 0) m.Jstar

end
-- END MODULE AttributedStationaryCriterion

-- BEGIN MODULE AccumulationOptimality
section

set_option autoImplicit false

namespace BertsekasShreve.Monotone

open Filter Topology

/-- Bertsekas & Shreve (1996), p. 87, Proposition 5.11, under the assumptions of Proposition 5.10
(p. 86): I, I.1 and I.2 hold, the control space `C` is a Hausdorff space, and for a nonnegative
integer `k̄` the sets `U_k(x, λ) = {u ∈ U(x) | H[x, u, T^k(J₀)] ≤ λ}` (eq. (40)) are compact for all
`x ∈ S`, `λ ∈ ℝ`, `k ≥ k̄`. Then
(a) some policy `π* = (μ₀*, μ₁*, …)` satisfies `(T_{μ_k*} T^k)(J₀) = T^{k+1}(J₀)` for all `k ≥ k̄`
(eq. (43));
(b) for every policy satisfying (43), `{μ_k*(x)}` has an accumulation point whenever
`J*(x) < ∞`;
(c) if `μ* : S → C` takes an accumulation point of `{μ_k*(x)}` at every `x` with `J*(x) < ∞` and a
value in `U(x)` at every `x` with `J*(x) = ∞`, then `μ*` is admissible and the stationary policy
`(μ*, μ*, …)` is optimal. -/
theorem prop5_11_accumulation_points_optimal {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : MonotoneDP.Increase.Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α)
    (kbar : ℕ)
    (hcpt : ∀ x : S, ∀ lam : ℝ, ∀ k : ℕ, kbar ≤ k →
      IsCompact {u | u ∈ m.U x ∧ m.H x u ((m.T)^[k] m.Jbar) ≤ (lam : EReal)}) :
    (∃ π : m.Policy, ∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) ∧
    (∀ π : m.Policy, (∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) →
      ∀ x : S, m.Jstar x < ⊤ → ∃ u : C, MapClusterPt u atTop (fun k => (π k).1 x)) ∧
    (∀ π : m.Policy, (∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) →
      ∀ μ : S → C,
        (∀ x : S, m.Jstar x < ⊤ → MapClusterPt (μ x) atTop (fun k => (π k).1 x)) →
        (∀ x : S, m.Jstar x = ⊤ → μ x ∈ m.U x) →
        ∃ hμ : ∀ x, μ x ∈ m.U x, m.Jmu ⟨μ, hμ⟩ = m.Jstar) := by
  have hm := MonotoneDP.Increase.Model.aux_p10_iter_mono (m := m) hI
  have hJ := MonotoneDP.Increase.Model.aux_p10_Jbar_le_Jstar (m := m) hI
  have hle : ∀ k, (m.T^[k] m.Jbar) ≤ m.Jstar := by
    intro k x
    apply le_trans _ (MonotoneDP.Increase.Model.aux_p10_Jinf_le_Jstar (m := m) hI x)
    rw [MonotoneDP.Increase.Model.aux_p10_Jinf_eq (m := m) hI x]
    exact le_iSup (fun N => (m.T^[N] m.Jbar) x) k
  have hc := MonotoneDP.Increase.prop12_compactness_convergence m hI hI1 hI2 ⟨kbar, hcpt⟩
  have hconv : m.Jinf = m.Jstar := hc.2.1.1.trans (hc.2.1.2.1.trans hc.2.1.2.2)
  refine ⟨Proof.exists_stage_minimizing_policy m kbar hcpt, ?_, ?_⟩
  · intro π hπ x hx
    exact Proof.minimizing_controls_cluster_exists m hm hJ hle kbar hcpt π hπ x hx
  · intro π hπ μ hcluster htop
    have hpoint : ∀ x, μ x ∈ m.U x ∧ m.H x (μ x) m.Jstar ≤ m.Jstar x := by
      intro x
      by_cases hx : m.Jstar x < ⊤
      · exact Proof.cluster_control_bellman_le m hI1 hm hJ hle hconv kbar hcpt π hπ
          x hx (μ x) (hcluster x hx)
      · have he : m.Jstar x = ⊤ := eq_top_iff.mpr (not_lt.mp hx)
        refine ⟨htop x he, ?_⟩
        rw [he]
        exact le_top
    let hμ : ∀ x, μ x ∈ m.U x := fun x => (hpoint x).1
    refine ⟨hμ, ((MonotoneDP.Increase.prop7_optimal_stationary_criterion m hI hI1 hI2).1
      ⟨μ, hμ⟩).mpr ?_⟩
    apply le_antisymm
    · rw [hc.2.1.2.2]
      exact fun x => (hpoint x).2
    · intro x
      exact iInf_le_of_le (μ x) (iInf_le_of_le (hμ x) le_rfl)


end BertsekasShreve.Monotone

end
-- END MODULE AccumulationOptimality

-- BEGIN MODULE PublicSolution
section

open BertsekasShreve.Monotone

open Filter Topology

/-- Bertsekas & Shreve (1996), p. 87, Proposition 5.11, under the assumptions of Proposition 5.10
(p. 86): I, I.1 and I.2 hold, the control space `C` is a Hausdorff space, and for a nonnegative
integer `k̄` the sets `U_k(x, λ) = {u ∈ U(x) | H[x, u, T^k(J₀)] ≤ λ}` (eq. (40)) are compact for all
`x ∈ S`, `λ ∈ ℝ`, `k ≥ k̄`. Then
(a) some policy `π* = (μ₀*, μ₁*, …)` satisfies `(T_{μ_k*} T^k)(J₀) = T^{k+1}(J₀)` for all `k ≥ k̄`
(eq. (43));
(b) for every policy satisfying (43), `{μ_k*(x)}` has an accumulation point whenever
`J*(x) < ∞`;
(c) if `μ* : S → C` takes an accumulation point of `{μ_k*(x)}` at every `x` with `J*(x) < ∞` and a
value in `U(x)` at every `x` with `J*(x) = ∞`, then `μ*` is admissible and the stationary policy
`(μ*, μ*, …)` is optimal. -/
theorem solution {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : MonotoneDP.Increase.Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α)
    (kbar : ℕ)
    (hcpt : ∀ x : S, ∀ lam : ℝ, ∀ k : ℕ, kbar ≤ k →
      IsCompact {u | u ∈ m.U x ∧ m.H x u ((m.T)^[k] m.Jbar) ≤ (lam : EReal)}) :
    (∃ π : m.Policy, ∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) ∧
    (∀ π : m.Policy, (∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) →
      ∀ x : S, m.Jstar x < ⊤ → ∃ u : C, MapClusterPt u atTop (fun k => (π k).1 x)) ∧
    (∀ π : m.Policy, (∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) →
      ∀ μ : S → C,
        (∀ x : S, m.Jstar x < ⊤ → MapClusterPt (μ x) atTop (fun k => (π k).1 x)) →
        (∀ x : S, m.Jstar x = ⊤ → μ x ∈ m.U x) →
        ∃ hμ : ∀ x, μ x ∈ m.U x, m.Jmu ⟨μ, hμ⟩ = m.Jstar) := by
  exact BertsekasShreve.Monotone.prop5_11_accumulation_points_optimal m hI hI1 hI2 kbar hcpt



end
-- END MODULE PublicSolution

#print axioms BertsekasShreve.Monotone.prop5_11_accumulation_points_optimal
#print axioms solution
