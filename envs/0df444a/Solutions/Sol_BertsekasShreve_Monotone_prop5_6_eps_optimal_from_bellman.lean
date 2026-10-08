-- Prove2me | solution 1 for BertsekasShreve.Monotone.prop5_6_eps_optimal_from_bellman
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:45:44.308858+00:00
-- url     : https://prove2.me/submissions/99377c31-247e-492a-ae6a-7c6add0e0940

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

set_option autoImplicit false

namespace P199db388

open Filter Topology MonotoneDP.Increase

variable {S C : Type*} (m : Model S C)

theorem limUnder_mono_eq {f : ℕ → EReal} (hf : Monotone f) :
    limUnder atTop f = ⨆ n, f n :=
  (tendsto_atTop_iSup hf).limUnder_eq

theorem Tmu_mono (μ : m.Selector) {J J' : S → EReal} (h : J ≤ J') :
    m.Tmu μ J ≤ m.Tmu μ J' :=
  fun x => m.mono x _ (μ.2 x) J J' h

theorem comp_mono (π : m.Policy) (N : ℕ) :
    ∀ {J J' : S → EReal}, J ≤ J' → m.comp π N J ≤ m.comp π N J' := by
  induction N with
  | zero => intro J J' h; exact h
  | succ N ih => intro J J' h; exact ih (Tmu_mono m (π N) h)

theorem Tmu_ge (hI : m.AssumptionI) (μ : m.Selector) {J : S → EReal} (h : m.Jbar ≤ J) :
    m.Jbar ≤ m.Tmu μ J :=
  fun x => (hI x _ (μ.2 x)).trans (Tmu_mono m μ h x)

theorem comp_ge (hI : m.AssumptionI) (π : m.Policy) (N : ℕ) :
    ∀ {J : S → EReal}, m.Jbar ≤ J → m.Jbar ≤ m.comp π N J := by
  induction N with
  | zero => intro J h; exact h
  | succ N ih => intro J h; exact ih (Tmu_ge m hI (π N) h)

theorem comp_succ_ge (hI : m.AssumptionI) (π : m.Policy) (N : ℕ) :
    m.comp π N m.Jbar ≤ m.comp π (N + 1) m.Jbar :=
  comp_mono m π N (Tmu_ge m hI (π N) le_rfl)

theorem comp_monotone (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Monotone (fun N => m.comp π N m.Jbar x) :=
  monotone_nat_of_le_succ fun N => comp_succ_ge m hI π N x

theorem Jpi_eq (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨆ N, m.comp π N m.Jbar x :=
  limUnder_mono_eq (comp_monotone m hI π x)

def shift (π : m.Policy) : m.Policy := fun k => π (k + 1)

theorem comp_succ_outer (π : m.Policy) (N : ℕ) :
    ∀ J : S → EReal, m.comp π (N + 1) J = m.Tmu (π 0) (m.comp (shift m π) N J) := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

theorem Jbar_le_Jstar (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  refine le_iInf fun π => ?_
  rw [Jpi_eq m hI]
  exact le_iSup (fun N => m.comp π N m.Jbar x) 0

theorem T_Jstar_le (hI : m.AssumptionI) (hI1 : m.AssumptionI1) : m.T m.Jstar ≤ m.Jstar := by
  intro x
  refine le_iInf fun π => ?_
  have hJs1 : ∀ k, m.Jbar ≤ m.comp (shift m π) k m.Jbar := fun k => comp_ge m hI _ k le_rfl
  have hJs2 : ∀ k, m.comp (shift m π) k m.Jbar ≤ m.comp (shift m π) (k + 1) m.Jbar :=
    fun k => comp_succ_ge m hI _ k
  have h1 := hI1 (fun k => m.comp (shift m π) k m.Jbar) hJs1 hJs2 x ((π 0).1 x) ((π 0).2 x)
  have hg : Monotone (fun k => m.H x ((π 0).1 x) (m.comp (shift m π) k m.Jbar)) := by
    intro a b hab
    exact m.mono x _ ((π 0).2 x) _ _ (comp_mono m (shift m π) _ le_rfl |>.trans
      ((monotone_nat_of_le_succ hJs2) hab))
  rw [limUnder_mono_eq hg] at h1
  have key : m.H x ((π 0).1 x) m.Jstar ≤ m.Jpi π x := by
    calc m.H x ((π 0).1 x) m.Jstar ≤ m.H x ((π 0).1 x) (m.Jpi (shift m π)) :=
          m.mono x _ ((π 0).2 x) _ _ (fun y => iInf_le (fun π' => m.Jpi π' y) (shift m π))
      _ = ⨆ k, m.H x ((π 0).1 x) (m.comp (shift m π) k m.Jbar) := h1.symm
      _ ≤ m.Jpi π x := by
          rw [Jpi_eq m hI]
          refine iSup_le fun k => ?_
          have := le_iSup (fun N => m.comp π N m.Jbar x) (k + 1)
          rw [comp_succ_outer] at this
          exact this
  exact (iInf₂_le ((π 0).1 x) ((π 0).2 x)).trans key

theorem comp_add_le (α : ℝ) (hI : m.AssumptionI) (hI2 : m.AssumptionI2 α) (π : m.Policy)
    (N : ℕ) : ∀ J : S → EReal, m.Jbar ≤ J → ∀ r : ℝ, 0 < r →
      m.comp π N (fun y => J y + (r : EReal)) ≤
        fun y => m.comp π N J y + ((α ^ N * r : ℝ) : EReal) := by
  induction N with
  | zero => intro J _ r _ y; simp [Model.comp]
  | succ N ih =>
    intro J hJ r hr
    show m.comp π N (m.Tmu (π N) (fun y => J y + (r : EReal))) ≤
      fun y => m.comp π N (m.Tmu (π N) J) y + ((α ^ (N + 1) * r : ℝ) : EReal)
    have h1 : m.Tmu (π N) (fun y => J y + (r : EReal)) ≤
        fun y => m.Tmu (π N) J y + ((α * r : ℝ) : EReal) :=
      fun y => (hI2.2 r hr J hJ y _ ((π N).2 y)).2
    have h2 := ih (m.Tmu (π N) J) (Tmu_ge m hI (π N) hJ) (α * r) (mul_pos hI2.1 hr)
    refine (comp_mono m π N h1).trans (h2.trans fun y => ?_)
    rw [show α ^ N * (α * r) = α ^ (N + 1) * r by ring]

theorem partA (α : ℝ) (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : m.AssumptionI2 α)
    (ε : ℝ) (εs : ℕ → ℝ) (hεs : ∀ i, 0 < εs i) (hsum : HasSum (fun k => α ^ k * εs k) ε)
    (π : m.Policy) (hπ : ∀ k : ℕ, m.Tmu (π k) m.Jstar ≤ fun x => m.T m.Jstar x + (εs k : EReal)) :
    m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal) := by
  refine ⟨fun x => iInf_le (fun π' => m.Jpi π' x) π, ?_⟩
  have hT := T_Jstar_le m hI hI1
  have hJ := Jbar_le_Jstar m hI
  have Q : ∀ N, m.comp π N m.Jstar ≤
      fun x => m.Jstar x + ((∑ k ∈ Finset.range N, α ^ k * εs k : ℝ) : EReal) := by
    intro N
    induction N with
    | zero => intro x; simp [Model.comp]
    | succ N ih =>
      have h1 : m.Tmu (π N) m.Jstar ≤ fun x => m.Jstar x + (εs N : EReal) :=
        fun x => (hπ N x).trans (add_le_add (hT x) le_rfl)
      have h2 := comp_add_le m α hI hI2 π N m.Jstar hJ (εs N) (hεs N)
      show m.comp π N (m.Tmu (π N) m.Jstar) ≤ _
      intro x
      refine ((comp_mono m π N h1).trans h2 x).trans ?_
      refine (add_le_add (ih x) le_rfl).trans (le_of_eq ?_)
      rw [Finset.sum_range_succ, EReal.coe_add, add_assoc]
  intro x
  rw [Jpi_eq m hI]
  refine iSup_le fun N => ?_
  refine (comp_mono m π N hJ x).trans ((Q N x).trans (add_le_add le_rfl ?_))
  refine EReal.coe_le_coe_iff.2 (sum_le_hasSum _ (fun i _ => ?_) hsum)
  exact (mul_pos (pow_pos hI2.1 i) (hεs i)).le

end P199db388

theorem solution {S C : Type*} (m : MonotoneDP.Increase.Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (α : ℝ) (hI2 : m.AssumptionI2 α) :
    (∀ ε : ℝ, 0 < ε → ∀ εs : ℕ → ℝ, (∀ i, 0 < εs i) → HasSum (fun k => α ^ k * εs k) ε →
      ∀ π : m.Policy, (∀ k : ℕ, m.Tmu (π k) m.Jstar ≤ fun x => m.T m.Jstar x + (εs k : EReal)) →
        m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal)) ∧
    (∀ ε : ℝ, 0 < ε → α < 1 → ∀ μ : m.Selector,
      m.Tmu μ m.Jstar ≤ (fun x => m.T m.Jstar x + ((ε * (1 - α) : ℝ) : EReal)) →
        m.Jstar ≤ m.Jmu μ ∧ m.Jmu μ ≤ fun x => m.Jstar x + (ε : EReal)) := by
  refine ⟨fun ε _ εs hεs hsum π hπ => P199db388.partA m α hI hI1 hI2 ε εs hεs hsum π hπ, ?_⟩
  intro ε hε hα μ hμ
  have h1α : 0 < 1 - α := by linarith
  have hsum : HasSum (fun k => α ^ k * (ε * (1 - α))) ε := by
    have := (hasSum_geometric_of_lt_one hI2.1.le hα).mul_right (ε * (1 - α))
    have e : (1 - α)⁻¹ * (ε * (1 - α)) = ε := by
      rw [mul_comm ε, ← mul_assoc, inv_mul_cancel₀ h1α.ne', one_mul]
    rwa [e] at this
  exact P199db388.partA m α hI hI1 hI2 ε (fun _ => ε * (1 - α)) (fun _ => mul_pos hε h1α) hsum
    (m.stationary μ) (fun _ => hμ)
