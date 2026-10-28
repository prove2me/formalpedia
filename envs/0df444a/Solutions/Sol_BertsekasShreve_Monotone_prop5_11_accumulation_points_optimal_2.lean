-- Prove2me | solution 2 for BertsekasShreve.Monotone.prop5_11_accumulation_points_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:14.909977+00:00
-- url     : https://prove2.me/submissions/e1fa5ed9-0b4d-4c4f-940e-033c680e3df9

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Increase_Epigraph
import Definitions.Def_MonotoneDP_Increase_Model
import Theorems.Thm_MonotoneDP_Increase_prop11_convergence_characterization
import Theorems.Thm_MonotoneDP_Increase_lemma2_projection_epigraph
import Theorems.Thm_MonotoneDP_Increase_lemma3_compact_sublevel_min
import Theorems.Thm_MonotoneDP_Increase_prop7_optimal_stationary_criterion

-- carved verbatim out of submission 32171cbc-d45c-48fd-ba5d-ff2a36c5096c, lines 1460-1486

section
set_option autoImplicit false
open Filter Topology
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

end

section
set_option autoImplicit false
open Filter Topology MonotoneDP.Increase
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

end

section
set_option autoImplicit false
open MonotoneDP
open MonotoneDP.Increase
open Filter Topology
open Model
variable {S C : Type*} (m : Model S C)

namespace MonotoneDP.Increase.Model

theorem aux_p10_T_mono : Monotone m.T := by
  intro J J' h x
  unfold T
  exact iInf₂_mono (fun u hu => m.mono x u hu J J' h)

end MonotoneDP.Increase.Model

end

section
set_option autoImplicit false
open MonotoneDP
open MonotoneDP.Increase
open Filter Topology
open Model
variable {S C : Type*} (m : Model S C)
variable {m}

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jbar_le_T (hI : m.AssumptionI) : m.Jbar ≤ m.T m.Jbar :=
  fun x => le_iInf₂ (fun u hu => hI x u hu)

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_iter_mono (hI : m.AssumptionI) : Monotone (fun N => (m.T)^[N] m.Jbar) :=
  Monotone.monotone_iterate_of_le_map m.aux_p10_T_mono (aux_p10_Jbar_le_T hI)

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jinf_eq (hI : m.AssumptionI) (x : S) :
    m.Jinf x = ⨆ N, (m.T)^[N] m.Jbar x := by
  unfold Jinf
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_p10_iter_mono hI hab x

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jbar_le_Jinf (hI : m.AssumptionI) : m.Jbar ≤ m.Jinf := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  exact le_iSup (fun N => (m.T)^[N] m.Jbar x) 0

end MonotoneDP.Increase.Model

end

section
set_option autoImplicit false
open MonotoneDP
open MonotoneDP.Increase
open Filter Topology
open Model
variable {S C : Type*} (m : Model S C)

namespace MonotoneDP.Increase.Model

theorem aux_p10_T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J := by
  intro x
  exact iInf₂_le (μ.1 x) (μ.2 x)

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

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

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_Tmu_mono (μ : m.Selector) : Monotone (m.Tmu μ) := by
  intro J J' h x
  exact m.mono x (μ.1 x) (μ.2 x) J J' h

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_comp_mono (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => intro J J' h; simpa [comp] using h
  | succ N ih =>
    intro J J' h
    simp only [comp]
    exact ih (m.aux_p10_Tmu_mono (π N) h)

end MonotoneDP.Increase.Model

end

section
set_option autoImplicit false
open MonotoneDP
open MonotoneDP.Increase
open Filter Topology
open Model
variable {S C : Type*} (m : Model S C)
variable {m}

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jbar_le_Tmu (hI : m.AssumptionI) (μ : m.Selector) :
    m.Jbar ≤ m.Tmu μ m.Jbar :=
  fun x => hI x (μ.1 x) (μ.2 x)

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_comp_Jbar_mono (hI : m.AssumptionI) (π : m.Policy) :
    Monotone (fun N => m.comp π N m.Jbar) := by
  apply monotone_nat_of_le_succ
  intro N
  show m.comp π N m.Jbar ≤ m.comp π N (m.Tmu (π N) m.Jbar)
  exact m.aux_p10_comp_mono π N (aux_p10_Jbar_le_Tmu hI _)

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jpi_eq (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨆ N, m.comp π N m.Jbar x := by
  unfold Jpi
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_p10_comp_Jbar_mono hI π hab x

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jinf_le_Jstar (hI : m.AssumptionI) : m.Jinf ≤ m.Jstar := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  refine iSup_le (fun N => le_iInf (fun π => ?_))
  rw [aux_p10_Jpi_eq hI]
  exact le_trans (m.aux_p10_iter_le_comp π N m.Jbar x)
    (le_iSup (fun N => m.comp π N m.Jbar x) N)

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

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

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

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

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jbar_le_Jpi (hI : m.AssumptionI) (π : m.Policy) : m.Jbar ≤ m.Jpi π := by
  intro x
  rw [aux_p10_Jpi_eq hI]
  exact le_iSup (fun N => m.comp π N m.Jbar x) 0

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_Jbar_le_Jstar (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar :=
  fun x => le_iInf (fun π => aux_p10_Jbar_le_Jpi hI π x)

end MonotoneDP.Increase.Model

end

section
set_option autoImplicit false
open MonotoneDP
open MonotoneDP.Increase
open Filter Topology
open Model
variable {S C : Type*} (m : Model S C)

namespace MonotoneDP.Increase.Model

def aux_p10_shift (π : m.Policy) : m.Policy := fun k => π (k + 1)

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_comp_succ (π : m.Policy) (N : ℕ) : ∀ J,
    m.comp π (N + 1) J = m.Tmu (π 0) (m.comp (m.aux_p10_shift π) N J) := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

end MonotoneDP.Increase.Model

end

section
set_option autoImplicit false
open MonotoneDP
open MonotoneDP.Increase
open Filter Topology
open Model
variable {S C : Type*} (m : Model S C)
variable {m}

namespace MonotoneDP.Increase.Model

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

end MonotoneDP.Increase.Model

namespace MonotoneDP.Increase.Model

theorem aux_p10_TJstar_eq (hI : m.AssumptionI) (hI1 : m.AssumptionI1)
    (hI2 : ∃ α : ℝ, m.AssumptionI2 α) : m.T m.Jstar = m.Jstar := by
  have h1 := aux_p10_TJstar_le hI hI1
  apply le_antisymm h1
  apply aux_p10_min hI hI2
  · exact (aux_p10_Jbar_le_T hI).trans (m.aux_p10_T_mono (aux_p10_Jbar_le_Jstar hI))
  · exact m.aux_p10_T_mono h1

end MonotoneDP.Increase.Model

end

section
set_option autoImplicit false
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

end

section
set_option autoImplicit false
open MonotoneDP.Increase Filter Topology

theorem T_mono {S C : Type*} (m : Model S C) : Monotone m.T := by
  intro J K h x
  exact iInf_mono (fun u => iInf_mono (fun hu => m.mono x u hu J K h))

theorem iterate_monotone {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    Monotone (fun k => m.T^[k] m.Jbar) :=
  (T_mono m).monotone_iterate_of_le_map (fun x => le_iInf (fun u => le_iInf (fun hu => hI x u hu)))

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
        exact (m.mono p.1 u hu.1 _ _ (iterate_monotone m hI (by omega : j+kbar ≤ j+1+kbar))).trans hu.2
      obtain ⟨u,hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hdec hnon (hK 0) (fun j => (hK j).isClosed)
      have huj := fun j => Set.mem_iInter.mp hu j
      refine ⟨u,(huj 0).1,Set.mem_iInter.mpr (fun k => Set.mem_iInter.mpr (fun hk => ?_))⟩
      refine ⟨(huj 0).1,?_⟩
      exact (m.mono p.1 u (huj 0).1 _ _ (iterate_monotone m hI (by omega : k-1 ≤ k+kbar))).trans (huj k).2
  have hh := MonotoneDP.Increase.prop11_convergence_characterization m hI hI1 hI2
  exact ⟨hp,(prop10_dp_limit_le_optimal m hI hI1 hI2).2.mpr (hh.2.1.mpr hp).1,(hh.2.2.mpr hp).2⟩

end

section
set_option autoImplicit false
open Filter Topology

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
  refine ⟨exists_stage_minimizing_policy m kbar hcpt, ?_, ?_⟩
  · intro π hπ x hx
    exact minimizing_controls_cluster_exists m hm hJ hle kbar hcpt π hπ x hx
  · intro π hπ μ hcluster htop
    have hpoint : ∀ x, μ x ∈ m.U x ∧ m.H x (μ x) m.Jstar ≤ m.Jstar x := by
      intro x
      by_cases hx : m.Jstar x < ⊤
      · exact cluster_control_bellman_le m hI1 hm hJ hle hconv kbar hcpt π hπ
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
  exact prop5_11_accumulation_points_optimal m hI hI1 hI2 kbar hcpt

end
