-- Prove2me | solution 2 for GallegoOzerADI.PositiveSetup.myopic_order_up_to_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:25.137671+00:00
-- url     : https://prove2.me/submissions/b568eebc-018c-494c-9084-51440e2aa5ee

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels
import Theorems.Thm_GallegoOzerADI_PositiveSetup_myopic_bounds
import Theorems.Thm_GallegoOzerADI_PositiveSetup_sS_policy_optimal

-- carved verbatim out of submission 0eed29c9-a9b3-4cb9-b81d-8140e6705f1c, lines 1358-1368

section
set_option autoImplicit false
open MeasureTheory
open GallegoOzerADI
open GallegoOzerADI.PositiveSetup
open Filter Topology
variable {L M : ℕ}

lemma aux_myb_Gprops {G : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ G)
    (hcoer : Tendsto G (cocompact ℝ) atTop) :
    (∀ x, G (myopicOrderUpTo G) ≤ G x) ∧
    (∀ y, y < myopicOrderUpTo G → G (myopicOrderUpTo G) < G y) ∧
    (∀ y y', y ≤ y' → y' ≤ myopicOrderUpTo G → G y' ≤ G y) ∧
    (∀ y y', myopicOrderUpTo G ≤ y → y ≤ y' → G y ≤ G y') := by
  have hGc : Continuous G := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  obtain ⟨y₀, hy₀⟩ := hGc.exists_forall_le hcoer
  have hne : ({y : ℝ | ∀ x, G y ≤ G x}).Nonempty := ⟨y₀, hy₀⟩
  have hbdd : BddBelow {y : ℝ | ∀ x, G y ≤ G x} := by
    have hev : ∀ᶠ y in cocompact ℝ, G y₀ < G y := hcoer.eventually_gt_atTop (G y₀)
    obtain ⟨Kc, hKc, hsub⟩ := mem_cocompact.1 hev
    refine hKc.bddBelow.mono fun y hy => ?_
    by_contra hyK
    have h1 : G y₀ < G y := hsub hyK
    have h2 : G y ≤ G y₀ := hy y₀
    linarith
  have hclosed : IsClosed {y : ℝ | ∀ x, G y ≤ G x} := by
    have : {y : ℝ | ∀ x, G y ≤ G x} = ⋂ x, {y | G y ≤ G x} := by ext y; simp
    rw [this]; exact isClosed_iInter fun x => isClosed_le hGc continuous_const
  have hmem : ∀ x, G (myopicOrderUpTo G) ≤ G x := hclosed.csInf_mem hne hbdd
  refine ⟨hmem, fun y hy => ?_, fun y y' h1 h2 => ?_, fun y y' h1 h2 => ?_⟩
  · by_contra h
    push Not at h
    have hyZ : y ∈ {y : ℝ | ∀ x, G y ≤ G x} := fun x => h.trans (hmem x)
    have := csInf_le hbdd hyZ
    unfold myopicOrderUpTo at hy
    linarith
  · have hz : y' ∈ segment ℝ y (myopicOrderUpTo G) := by
      rw [segment_eq_Icc (h1.trans h2)]; exact ⟨h1, h2⟩
    have := hconv.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hz
    exact this.trans (max_le le_rfl (hmem y))
  · have hz : y ∈ segment ℝ (myopicOrderUpTo G) y' := by
      rw [segment_eq_Icc (h1.trans h2)]; exact ⟨h1, h2⟩
    have := hconv.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hz
    exact this.trans (max_le (hmem y') le_rfl)

lemma aux_myb_obs_nonneg {o : Fin M → ℝ} (ho : ∀ j, 0 ≤ o j) (j : ℕ) : 0 ≤ obsComp o j := by
  unfold obsComp; split_ifs
  · exact ho _
  · exact le_refl _

lemma aux_myb_nextO_nonneg {o : Fin M → ℝ} (ho : ∀ j, 0 ≤ o j) {D : Fin (L + M + 2) → ℝ}
    (hD : ∀ k, 0 ≤ D k) : ∀ j, 0 ≤ nextO o D j := fun j => by
  unfold nextO
  exact add_nonneg (aux_myb_obs_nonneg ho _) (hD _)

end

section
set_option autoImplicit false
open MeasureTheory
open GallegoOzerADI
open GallegoOzerADI.PositiveSetup
variable {L M : ℕ} [NeZero M]

theorem nextX_le_myopic_reorder (G : ℝ → ℝ) (K α : ℝ)
    (o : Fin M → ℝ) (D : Fin (L+M+2) → ℝ) (hD : ∀ k,0 ≤ D k)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0)
    (y : ℝ) (hy : y ≤ myopicUpperLevel G K α) :
    nextX y o D ≤ myopicReorderPoint G K := by
  have hsum : 0 ≤ ∑ k : Fin (L+2), D (Fin.castLE (by omega) k) :=
    Finset.sum_nonneg (fun k _ => hD _)
  have hzero : obsComp o 0 = o 0 := by simp [obsComp,NeZero.pos M]
  unfold nextX
  rw [hzero]
  linarith

theorem continuation_eq_ae (P : Model L M) (G : ℝ → ℝ) (K α : ℝ)
    (ν : Measure (Fin (L+M+2) → ℝ)) (hG : ∀ t,P.G t=G) (hK : ∀ t,P.K t=K)
    (hα : ∀ t,P.α t=α) (hμ : ∀ t,P.μ t=ν)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ)
    (ho : ∀ j,0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0)
    (a b : ℝ) (ha : a ≤ myopicUpperLevel G K α) (hb : b ≤ myopicUpperLevel G K α) :
    (fun D => P.J (t+1) (nextX a o D) (nextO o D)) =ᵐ[P.μ t]
      (fun D => P.J (t+1) (nextX b o D) (nextO o D)) := by
  by_cases ht : t=P.T
  · subst t
    exact Filter.Eventually.of_forall (fun D => by simp only [P.J_terminal])
  · have hn : t+1 ≤ P.T := by omega
    have htNext : 1 ≤ t+1 := ht1.trans (Nat.le_succ t)
    filter_upwards [P.μ_nonneg t] with D hD
    have hon := aux_myb_nextO_nonneg ho hD
    obtain ⟨S,s,hS,hs,hpolicy⟩ := GallegoOzerADI.PositiveSetup.sS_policy_optimal P (t+1) htNext hn (nextO o D)
    have hbounds := GallegoOzerADI.PositiveSetup.myopic_bounds P G K α ν hG hK hα hμ (t+1) htNext hn
      (nextO o D) hon S s hS hs
    have hxa : nextX a o D ≤ s :=
      (nextX_le_myopic_reorder G K α o D hD hobs a ha).trans hbounds.2.2
    have hxb : nextX b o D ≤ s :=
      (nextX_le_myopic_reorder G K α o D hD hobs b hb).trans hbounds.2.2
    exact ((hpolicy (nextX a o D)).1 hxa).2.trans (((hpolicy (nextX b o D)).1 hxb).2.symm)

end

section
set_option autoImplicit false
open MeasureTheory Filter
open GallegoOzerADI
open GallegoOzerADI.PositiveSetup

theorem myopic_order_up_to_isLeast {L M : ℕ} [NeZero M] (P : Model L M)
    (G : ℝ → ℝ) (K α : ℝ) (ν : Measure (Fin (L+M+2) → ℝ))
    (hG : ∀ t,P.G t=G) (hK : ∀ t,P.K t=K) (hα : ∀ t,P.α t=α) (hμ : ∀ t,P.μ t=ν)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : ∀ j,0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0) :
    IsLeast {y | ∀ x,P.V t y o ≤ P.V t x o} (myopicOrderUpTo G) := by
  obtain ⟨S,s,hS,hs,_⟩ := GallegoOzerADI.PositiveSetup.sS_policy_optimal P t ht1 htT o
  have hb := GallegoOzerADI.PositiveSetup.myopic_bounds P G K α ν hG hK hα hμ t ht1 htT o ho S s hS hs
  have hconv : ConvexOn ℝ Set.univ G := by
    rw [← hG 0]
    exact P.G_convex 0
  have hcoer : Tendsto G (cocompact ℝ) atTop := by
    rw [← hG 0]
    exact P.G_coercive 0
  have hmin := (aux_myb_Gprops hconv hcoer).1
  have he := continuation_eq_ae P G K α ν hG hK hα hμ t ht1 htT o ho hobs
    (myopicOrderUpTo G) S (hb.1.trans hb.2.1) hb.2.1
  have hint := integral_congr_ae he
  have hcost : P.V t (myopicOrderUpTo G) o ≤ P.V t S o := by
    unfold Model.V
    simp only [hG t,hint]
    exact add_le_add (hmin S) le_rfl
  have hglobal : ∀ x,P.V t (myopicOrderUpTo G) o ≤ P.V t x o :=
    fun x => hcost.trans (hS.1 x)
  have heq : S=myopicOrderUpTo G := le_antisymm (hS.2 hglobal) hb.1
  simpa only [heq] using hS

end

section
set_option autoImplicit false
open MeasureTheory
open GallegoOzerADI
open GallegoOzerADI.PositiveSetup

theorem myopic_order_up_to_optimal {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ)
    (K α : ℝ) (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G)
    (hK : ∀ t, P.K t = K) (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0) :
    IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} (myopicOrderUpTo G) := by
  exact myopic_order_up_to_isLeast
    P G K α ν hG hK hα hμ t ht₁ htT o ho hobs

end

section
set_option autoImplicit false
open GallegoOzerADI.PositiveSetup
open MeasureTheory

theorem solution {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ)
    (K α : ℝ) (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G)
    (hK : ∀ t, P.K t = K) (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0) :
    IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} (myopicOrderUpTo G) := by
  exact myopic_order_up_to_optimal P G K α ν hG hK hα hμ t ht₁ htT o ho hobs

end
