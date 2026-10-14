-- Prove2me | solution 1 for BertsekasShreve.Monotone.cor5_7_1_finite_state_eps_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:29:03.761071+00:00
-- url     : https://prove2.me/submissions/53365820-9d69-4db9-9b37-27bc5705d981

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

open Filter Topology

namespace BertsekasShreve.Monotone
end BertsekasShreve.Monotone

namespace MonotoneDP.Decrease.Model

variable {S C : Type*} (m : MonotoneDP.Decrease.Model S C)

theorem d53_monoT : Monotone m.T := by
  intro J J' h x
  exact iInf₂_mono fun u hu => m.mono x u hu J J' h

theorem d53_monoTmu (μ : m.Selector) : Monotone (m.Tmu μ) := by
  intro J J' h x
  exact m.mono x (μ.1 x) (μ.2 x) J J' h

theorem d53_T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J := by
  intro x
  exact iInf₂_le (μ.1 x) (μ.2 x)

theorem d53_comp_mono (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => intro J J' h; exact h
  | succ N ih =>
    intro J J' h
    exact ih (m.d53_monoTmu (π N) h)

theorem d53_comp_succ (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp π (N + 1) J = m.Tmu (π 0) (m.comp (fun k => π (k + 1)) N J) := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih =>
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

theorem d53_comp_anti (hD : m.AssumptionD) (π : m.Policy) (N : ℕ) :
    m.comp π (N + 1) m.Jbar ≤ m.comp π N m.Jbar := by
  show m.comp π N (m.Tmu (π N) m.Jbar) ≤ _
  apply m.d53_comp_mono π N
  intro x
  exact hD x _ ((π N).2 x)

theorem d53_tendsto (hD : m.AssumptionD) (π : m.Policy) (x : S) :
    Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (m.Jpi π x)) := by
  have hanti : Antitone (fun N => m.comp π N m.Jbar x) :=
    antitone_nat_of_succ_le fun n => m.d53_comp_anti hD π n x
  have h := tendsto_atTop_iInf hanti
  have : m.Jpi π x = ⨅ N, m.comp π N m.Jbar x := h.limUnder_eq
  rw [this]
  exact h

theorem d53_Jpi_eq (hD : m.AssumptionD) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨅ N, m.comp π N m.Jbar x :=
  (tendsto_atTop_iInf (antitone_nat_of_succ_le fun n => m.d53_comp_anti hD π n x)).limUnder_eq

theorem d53_comp_le_Jbar (hD : m.AssumptionD) (π : m.Policy) (N : ℕ) :
    m.comp π N m.Jbar ≤ m.Jbar := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact (m.d53_comp_anti hD π N).trans ih



theorem d53_iter_le_comp (π : m.Policy) (N : ℕ) (J : S → EReal) :
    (m.T)^[N] J ≤ m.comp π N J := by
  induction N generalizing J with
  | zero => exact le_rfl
  | succ N ih =>
    show (m.T)^[N] (m.T J) ≤ m.comp π N (m.Tmu (π N) J)
    exact ((m.d53_monoT.iterate N) (m.d53_T_le_Tmu (π N) J)).trans (ih _)

theorem d53_maximal (hD : m.AssumptionD) (J : S → EReal) (hJ : J ≤ m.Jbar)
    (hT : J ≤ m.T J) : J ≤ m.Jstar := by
  have hiter : ∀ N, J ≤ (m.T)^[N] J := by
    intro N
    induction N with
    | zero => exact le_rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply']
      exact hT.trans (m.d53_monoT ih)
  intro x
  refine le_iInf fun π => ?_
  rw [m.d53_Jpi_eq hD π x]
  refine le_iInf fun N => ?_
  exact ((hiter N).trans ((m.d53_iter_le_comp π N J).trans
    (m.d53_comp_mono π N hJ))) x

theorem d53_le_of_eps {A B : EReal} (h : ∀ ε : ℝ, 0 < ε → A ≤ B + (ε : EReal)) : A ≤ B := by
  induction B using EReal.rec with
  | bot => simpa using h 1 one_pos
  | top => exact le_top
  | coe b =>
    refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
    have hz' : b < z := by exact_mod_cast hz
    have := h (z - b) (by linarith)
    rw [← EReal.coe_add] at this
    simpa using this

theorem d53_T_Jbar_le (hD : m.AssumptionD) : m.T m.Jbar ≤ m.Jbar := by
  intro x
  obtain ⟨u, hu⟩ := m.U_nonempty x
  exact (iInf₂_le u hu).trans (hD x u hu)

theorem d53_iter_anti (hD : m.AssumptionD) : Antitone (fun N => (m.T)^[N] m.Jbar) :=
  Monotone.antitone_iterate_of_map_le m.d53_monoT (m.d53_T_Jbar_le hD)

theorem d53_iter_le_Jbar (hD : m.AssumptionD) (N : ℕ) : (m.T)^[N] m.Jbar ≤ m.Jbar :=
  m.d53_iter_anti hD (Nat.zero_le N)

/-- D.2 one-step estimate. -/
theorem d53_step {α : ℝ} (hD2 : m.AssumptionD2 α) {δ : ℝ} (hδ : 0 < δ) {J G : S → EReal}
    (hJ : J ≤ m.Jbar) (hJG : ∀ y, J y ≤ G y + (δ : EReal)) (x : S) (u : C) (hu : u ∈ m.U x) :
    m.H x u J ≤ m.H x u G + ((α * δ : ℝ) : EReal) := by
  have h1 := (hD2.2 δ hδ J hJ x u hu).1
  have h2 : (fun y => J y - (δ : EReal)) ≤ G := by
    intro y
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]
    exact hJG y
  have h3 := h1.trans (m.mono x u hu _ _ h2)
  rwa [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))] at h3

theorem d53_selector (G : S → EReal) (hG : ∀ y, m.T G y ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : m.Selector, ∀ y, m.H y (μ.1 y) G ≤ m.T G y + (ε : EReal) := by
  have h : ∀ y, ∃ u ∈ m.U y, m.H y u G ≤ m.T G y + (ε : EReal) := by
    intro y
    by_cases htop : m.T G y = ⊤
    · obtain ⟨u, hu⟩ := m.U_nonempty y
      refine ⟨u, hu, ?_⟩
      rw [htop, EReal.top_add_coe]
      exact le_top
    · obtain ⟨a, ha⟩ : ∃ a : ℝ, m.T G y = a :=
        ⟨(m.T G y).toReal, (EReal.coe_toReal htop (hG y)).symm⟩
      have hlt : m.T G y < m.T G y + (ε : EReal) := by
        rw [ha, ← EReal.coe_add]
        exact_mod_cast (by linarith : a < a + ε)
      have hlt2 := hlt
      conv_lhs at hlt2 => rw [MonotoneDP.Decrease.Model.T]
      simp only [iInf_lt_iff] at hlt2
      obtain ⟨u, hu, hlt'⟩ := hlt2
      exact ⟨u, hu, hlt'.le⟩
  choose f hf using h
  exact ⟨⟨f, fun x => (hf x).1⟩, fun x => (hf x).2⟩

/-- prepend a selector to a policy -/
def d53_cons (μ : m.Selector) (π : m.Policy) : m.Policy := fun k =>
  match k with
  | 0 => μ
  | k + 1 => π k

theorem d53_comp_cons (μ : m.Selector) (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp (m.d53_cons μ π) (N + 1) J = m.Tmu μ (m.comp π N J) := by
  rw [m.d53_comp_succ]
  rfl

theorem d53_Jpi_le_comp (hD : m.AssumptionD) (π : m.Policy) (N : ℕ) :
    m.Jpi π ≤ m.comp π N m.Jbar := by
  intro x
  rw [m.d53_Jpi_eq hD π x]
  exact iInf_le (fun N => m.comp π N m.Jbar x) N

theorem d53_finite_horizon (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α)
    (hfin : ∀ x : S, ⊥ < m.Jstar x) (N : ℕ) :
    (∀ y, (m.T)^[N] m.Jbar y ≠ ⊥) ∧
      ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy, ∀ y, m.comp π N m.Jbar y ≤ (m.T)^[N] m.Jbar y + (ε : EReal) := by
  obtain ⟨α, hα2⟩ := hD2
  have hα : 0 < α := hα2.1
  have μ0 : m.Selector := ⟨fun y => (m.U_nonempty y).choose, fun y => (m.U_nonempty y).choose_spec⟩
  induction N with
  | zero =>
    refine ⟨fun y => m.Jbar_ne_bot y, fun ε hε => ⟨fun _ => μ0, fun y => ?_⟩⟩
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hε.le)
  | succ N ih =>
    obtain ⟨hnb, hpol⟩ := ih
    have hsucc : ∀ y, (m.T)^[N + 1] m.Jbar y = m.T ((m.T)^[N] m.Jbar) y := by
      intro y; rw [Function.iterate_succ_apply']
    have hnb' : ∀ y, (m.T)^[N + 1] m.Jbar y ≠ ⊥ := by
      intro x hx
      rw [hsucc] at hx
      obtain ⟨π', hπ'⟩ := hpol 1 one_pos
      have : m.Jstar x = ⊥ := by
        rw [EReal.eq_bot_iff_forall_lt]
        intro K
        have hlt : m.T ((m.T)^[N] m.Jbar) x < ((K - α : ℝ) : EReal) := by
          rw [hx]; exact EReal.bot_lt_coe _
        conv_lhs at hlt => rw [MonotoneDP.Decrease.Model.T]
        simp only [iInf_lt_iff] at hlt
        obtain ⟨u, hu, hlt'⟩ := hlt
        classical
        let μ : m.Selector := ⟨Function.update μ0.1 x u, by
          intro y
          by_cases hy : y = x
          · subst hy; simpa using hu
          · simpa [hy] using μ0.2 y⟩
        have hμx : μ.1 x = u := by simp [μ]
        calc m.Jstar x ≤ m.Jpi (m.d53_cons μ π') x := iInf_le (fun π => m.Jpi π x) _
          _ ≤ m.comp (m.d53_cons μ π') (N + 1) m.Jbar x := m.d53_Jpi_le_comp hD _ _ x
          _ = m.H x u (m.comp π' N m.Jbar) := by rw [m.d53_comp_cons]; simp [Tmu, hμx]
          _ ≤ m.H x u ((m.T)^[N] m.Jbar) + ((α * 1 : ℝ) : EReal) :=
              m.d53_step hα2 one_pos (m.d53_comp_le_Jbar hD π' N) (fun y => hπ' y) x u hu
          _ < ((K - α : ℝ) : EReal) + ((α * 1 : ℝ) : EReal) := by
              apply EReal.add_lt_add_right_coe hlt'
          _ = K := by rw [← EReal.coe_add]; congr 1; ring
      exact (ne_of_gt (hfin x)) this
    refine ⟨hnb', fun ε hε => ?_⟩
    obtain ⟨π', hπ'⟩ := hpol (ε / (2 * α)) (by positivity)
    obtain ⟨μ, hμ⟩ := m.d53_selector ((m.T)^[N] m.Jbar)
      (fun y => by rw [← hsucc]; exact hnb' y) (ε / 2) (by positivity)
    refine ⟨m.d53_cons μ π', fun y => ?_⟩
    rw [m.d53_comp_cons, hsucc]
    calc m.Tmu μ (m.comp π' N m.Jbar) y = m.H y (μ.1 y) (m.comp π' N m.Jbar) := rfl
      _ ≤ m.H y (μ.1 y) ((m.T)^[N] m.Jbar) + ((α * (ε / (2 * α)) : ℝ) : EReal) :=
          m.d53_step hα2 (by positivity) (m.d53_comp_le_Jbar hD π' N) (fun z => hπ' z) y _ (μ.2 y)
      _ ≤ (m.T ((m.T)^[N] m.Jbar) y + ((ε / 2 : ℝ) : EReal)) + ((α * (ε / (2 * α)) : ℝ) : EReal) := by
          gcongr
          exact hμ y
      _ = m.T ((m.T)^[N] m.Jbar) y + (ε : EReal) := by
          rw [add_assoc, ← EReal.coe_add]
          congr 2
          field_simp
          ring

theorem d53_Jstar_le_iter (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α)
    (hfin : ∀ x : S, ⊥ < m.Jstar x) (N : ℕ) : m.Jstar ≤ (m.T)^[N] m.Jbar := by
  intro x
  apply d53_le_of_eps
  intro ε hε
  obtain ⟨π, hπ⟩ := (m.d53_finite_horizon hD hD2 hfin N).2 ε hε
  exact (iInf_le (fun π => m.Jpi π x) π).trans ((m.d53_Jpi_le_comp hD π N x).trans (hπ x))

theorem d53_Jstar_eq_iInf (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α)
    (hfin : ∀ x : S, ⊥ < m.Jstar x) (x : S) : m.Jstar x = ⨅ N, (m.T)^[N] m.Jbar x := by
  refine le_antisymm (le_iInf fun N => m.d53_Jstar_le_iter hD hD2 hfin N x) ?_
  refine le_iInf fun π => ?_
  rw [m.d53_Jpi_eq hD π x]
  exact iInf_mono fun N => m.d53_iter_le_comp π N m.Jbar x

theorem d53_uniform [Finite S] (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α)
    (hfin : ∀ x : S, ⊥ < m.Jstar x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ y, (m.T)^[N] m.Jbar y ≤ m.Jstar y + (δ : EReal) := by
  have h : ∀ y, ∀ᶠ N in atTop, (m.T)^[N] m.Jbar y ≤ m.Jstar y + (δ : EReal) := by
    intro y
    by_cases htop : m.Jstar y = ⊤
    · refine Filter.Eventually.of_forall fun N => ?_
      rw [htop, EReal.top_add_coe]; exact le_top
    · obtain ⟨a, ha⟩ : ∃ a : ℝ, m.Jstar y = a :=
        ⟨(m.Jstar y).toReal, (EReal.coe_toReal htop (ne_of_gt (hfin y))).symm⟩
      have hlt : m.Jstar y < m.Jstar y + (δ : EReal) := by
        rw [ha, ← EReal.coe_add]
        exact_mod_cast (by linarith : a < a + δ)
      have hlt2 := hlt
      conv_lhs at hlt2 => rw [m.d53_Jstar_eq_iInf hD hD2 hfin y]
      rw [iInf_lt_iff] at hlt2
      obtain ⟨N0, hN0⟩ := hlt2
      exact Filter.eventually_atTop.2 ⟨N0, fun N hN => ((m.d53_iter_anti hD hN y).trans hN0.le)⟩
  exact (Filter.eventually_all.2 h).exists

theorem d53_bellman [Finite S] (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α)
    (hfin : ∀ x : S, ⊥ < m.Jstar x) : m.Jstar = m.T m.Jstar := by
  funext x
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun u hu => ?_
    obtain ⟨α, hα2⟩ := hD2
    have hα : 0 < α := hα2.1
    apply d53_le_of_eps
    intro ε hε
    obtain ⟨N, hN⟩ := m.d53_uniform hD ⟨α, hα2⟩ hfin (ε / α) (by positivity)
    calc m.Jstar x ≤ (m.T)^[N + 1] m.Jbar x := m.d53_Jstar_le_iter hD ⟨α, hα2⟩ hfin (N + 1) x
      _ = m.T ((m.T)^[N] m.Jbar) x := by rw [Function.iterate_succ_apply']
      _ ≤ m.H x u ((m.T)^[N] m.Jbar) := iInf₂_le u hu
      _ ≤ m.H x u m.Jstar + ((α * (ε / α) : ℝ) : EReal) :=
          m.d53_step hα2 (by positivity) (m.d53_iter_le_Jbar hD N) hN x u hu
      _ = m.H x u m.Jstar + (ε : EReal) := by congr 2; field_simp
  · rw [m.d53_Jstar_eq_iInf hD hD2 hfin x]
    refine le_iInf fun N => ?_
    cases N with
    | zero =>
      exact (m.d53_monoT (fun y => m.d53_Jstar_le_iter hD hD2 hfin 0 y) x).trans
        (m.d53_T_Jbar_le hD x)
    | succ N =>
      rw [Function.iterate_succ_apply']
      exact m.d53_monoT (m.d53_Jstar_le_iter hD hD2 hfin N) x

end MonotoneDP.Decrease.Model

namespace BertsekasShreve.Monotone

open MonotoneDP.Decrease

theorem cor5_3_1_core {S C : Type*} [Finite S]
    (m : MonotoneDP.Decrease.Model S C)
    (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α) (hfin : ∀ x : S, ⊥ < m.Jstar x) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.T J' → J' ≤ m.Jstar :=
  ⟨m.d53_bellman hD hD2 hfin, fun J' h1 h2 => m.d53_maximal hD J' h1 h2⟩

theorem cor5_7_1_core {S C : Type*} [Finite S]
    (m : MonotoneDP.Decrease.Model S C)
    (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α) (hfin : ∀ x : S, ⊥ < m.Jstar x) :
    ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
      m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal) := by
  intro ε hε
  obtain ⟨N, hN⟩ := m.d53_uniform hD hD2 hfin (ε / 2) (by positivity)
  obtain ⟨π, hπ⟩ := (m.d53_finite_horizon hD hD2 hfin N).2 (ε / 2) (by positivity)
  refine ⟨π, fun x => iInf_le (fun π => m.Jpi π x) π, fun y => ?_⟩
  calc m.Jpi π y ≤ m.comp π N m.Jbar y := m.d53_Jpi_le_comp hD π N y
    _ ≤ (m.T)^[N] m.Jbar y + ((ε / 2 : ℝ) : EReal) := hπ y
    _ ≤ (m.Jstar y + ((ε / 2 : ℝ) : EReal)) + ((ε / 2 : ℝ) : EReal) := by gcongr; exact hN y
    _ = m.Jstar y + (ε : EReal) := by
        rw [add_assoc, ← EReal.coe_add]; congr 2; ring

end BertsekasShreve.Monotone

open BertsekasShreve.Monotone


theorem solution {S C : Type*} [Finite S]
    (m : MonotoneDP.Decrease.Model S C)
    (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α) (hfin : ∀ x : S, ⊥ < m.Jstar x) :
    ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
      m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal) := by
  exact cor5_7_1_core m hD hD2 hfin
