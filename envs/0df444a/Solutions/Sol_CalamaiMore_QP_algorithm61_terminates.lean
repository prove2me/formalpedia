-- Prove2me | solution 1 for CalamaiMore.QP.algorithm61_terminates
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:34:06.719081+00:00
-- url     : https://prove2.me/submissions/e201a098-0a88-4899-9a11-2158898517a5

import Definitions.Def_CalamaiMore_QP_IsQuadratic
import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Lemmas
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_CalamaiMore_QP_IsAlgorithm61Run
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
open Set

private theorem finite_states_terminate {σ : Type*} [Finite σ]
    (F : ℕ → ℝ) (W : ℕ → σ) (good stop : ℕ → Prop)
    (hfreq : ∀ N,∃ k,N ≤ k ∧ good k) (hmono : Antitone F)
    (hvalue : ∀ i j,good i → good j → W i=W j → F i=F j)
    (hdrop : ∀ i,good i → ¬stop i → F (i+1)<F i) : ∃ k,stop k := by
  classical
  let S : Set σ := W '' {k | good k}
  have hn : S.Nonempty := by
    obtain ⟨k,_,hk⟩:=hfreq 0
    exact ⟨W k,k,hk,rfl⟩
  have hex : ∀ w : S,∃ k,good k ∧ W k=w := by
    intro w
    obtain ⟨k,hk,hw⟩:=w.property
    exact ⟨k,hk,hw⟩
  choose idx hidx using hex
  obtain ⟨w,hw,hmin⟩:=Set.exists_min_image (univ : Set S) (fun w => F (idx w)) (Set.toFinite _)
    ⟨⟨hn.choose,hn.choose_spec⟩,mem_univ _⟩
  by_contra hnone
  push_neg at hnone
  obtain ⟨j,hj,hgood⟩:=hfreq (idx w+1)
  have hjS : W j ∈ S := ⟨j,hgood,rfl⟩
  have heq : F (idx ⟨W j,hjS⟩)=F j :=
    hvalue _ _ (hidx _).1 hgood (hidx _).2
  have hh:=hmin ⟨W j,hjS⟩ (mem_univ _)
  rw [heq] at hh
  have hle:=hmono hj
  have hlt:=hdrop (idx w) (hidx w).1 (hnone _)
  linarith

private theorem frequent_minimum {m : ℕ} (W : ℕ → Finset (Fin m)) (good : ℕ → Prop)
    (hstep : ∀ k,¬good k → W k ⊆ W (k+1) ∧ (W (k+1)=W k → good (k+1))) :
    ∀ N,∃ k,N ≤ k ∧ good k := by
  classical
  intro N
  by_contra hnone
  push_neg at hnone
  have hcard : ∀ n,n ≤ (W (N+n)).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hbad:=hnone (N+n) (by omega)
      have hh:=hstep (N+n) hbad
      have hne : W (N+n) ≠ W (N+n+1) := by
        intro heq
        exact hnone _ (by omega) (hh.2 heq.symm)
      have hlt:=Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hh.1,hne⟩)
      have heq : N+(n+1)=N+n+1 := by omega
      rw [heq]
      omega
  have hh:=hcard (m+1)
  have hb:=(W (N+(m+1))).card_le_univ
  simp only [Fintype.card_fin] at hb
  omega
open Set

private theorem nearest_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (y : E) :
    CalamaiMore.Convergence.nearestPoint Ω y ∈ Ω ∧ ∀ w ∈ Ω,
      ‖CalamaiMore.Convergence.nearestPoint Ω y-y‖ ≤ ‖w-y‖ := by
  have he : ∃ z ∈ Ω,∀ w ∈ Ω,‖z-y‖ ≤ ‖w-y‖ := by
    obtain ⟨z,hz,hmin⟩:=exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv y
    refine ⟨z,hz,?_⟩
    intro w hw
    rw [norm_sub_rev z y,norm_sub_rev w y,hmin]
    exact ciInf_le (f:=fun w : Ω => ‖y-w‖) ⟨(0:ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩ ⟨w,hw⟩
  unfold CalamaiMore.Convergence.nearestPoint
  rw [dif_pos he]
  exact Classical.choose_spec he

private theorem nearest_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (y : E) :
    ∀ w ∈ Ω, inner ℝ (y-CalamaiMore.Convergence.nearestPoint Ω y)
      (w-CalamaiMore.Convergence.nearestPoint Ω y) ≤ 0 := by
  letI : Nonempty Ω := hne.to_subtype
  obtain ⟨hp,hmin⟩:=nearest_spec Ω hne hc hv y
  apply (norm_eq_iInf_iff_real_inner_le_zero hv hp).mp
  apply le_antisymm
  · apply le_ciInf
    intro w
    simpa only [norm_sub_rev] using hmin w w.property
  · exact ciInf_le (f:=fun w : Ω => ‖y-w‖) ⟨(0:ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩ ⟨_,hp⟩

private theorem poly_closed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) : IsClosed (CalamaiMore.QP.polyhedron c δ) := by
  simp only [CalamaiMore.QP.polyhedron,setOf_forall]
  exact isClosed_iInter fun j => isClosed_le continuous_const
    (show Continuous (fun x : E => inner ℝ (c j) x) from continuous_const.inner continuous_id)

private theorem poly_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ) : Convex ℝ (CalamaiMore.QP.polyhedron c δ) := by
  intro x hx y hy a b ha hb hab j
  simp only [inner_add_right,real_inner_smul_right]
  have h1:=mul_le_mul_of_nonneg_left (hx j) ha
  have h2:=mul_le_mul_of_nonneg_left (hy j) hb
  have he : (a+b)*δ j=δ j := by rw [hab,one_mul]
  nlinarith

private theorem projected_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) {x : E} (hx : x ∈ Ω) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    (α : ℝ) (hα : 0 < α) :
    inner ℝ (gradient f x) (CalamaiMore.QP.projPath f Ω x α-x) ≤ 0 ∧
    (¬CalamaiMore.Shared.IsStationaryPoint f Ω x →
      inner ℝ (gradient f x) (CalamaiMore.QP.projPath f Ω x α-x) < 0) := by
  let p := CalamaiMore.QP.projPath f Ω x α
  have hi:=nearest_inner Ω ⟨x,hx⟩ hc hv (x-α • gradient f x)
  change ∀ w ∈ Ω,inner ℝ (x-α • gradient f x-p) (w-p) ≤ 0 at hi
  have hix:=hi x hx
  have he1 : x-α • gradient f x-p = -(p-x)-α • gradient f x := by module
  have he2 : x-p = -(p-x) := by module
  rw [he1,he2,inner_sub_left,inner_neg_left,inner_neg_right,inner_neg_right,
    real_inner_smul_left,real_inner_self_eq_norm_sq] at hix
  have hnon : inner ℝ (gradient f x) (p-x) ≤ 0 := by nlinarith [sq_nonneg ‖p-x‖]
  refine ⟨hnon,?_⟩
  intro hnot
  have hne : p ≠ x := by
    intro heq
    apply hnot
    refine ⟨hx,?_⟩
    intro w hw
    have hh:=hi w hw
    rw [heq] at hh
    have he : x-α • gradient f x-x = -α • gradient f x := by module
    rw [he,real_inner_smul_left] at hh
    nlinarith
  have hn : 0 < ‖p-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith
open CalamaiMore.QP
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (f : E → ℝ) (hf : IsQuadratic f) (hbdd : BddBelow (f '' polyhedron c δ))
    (γ₁ γ₂ γ₃ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (W : ℕ → Finset (Fin m)) (α : ℕ → ℝ)
    (hrun : IsAlgorithm61Run f c δ γ₁ γ₂ γ₃ μ₁ μ₂ x W α) :
    ∃ l : ℕ, CalamaiMore.Shared.IsStationaryPoint f (polyhedron c δ) (x l) := by
  classical
  let good := fun k => IsWorkingSetMinimizer f c δ (W k) (x k)
  let stop := fun k => CalamaiMore.Shared.IsStationaryPoint f (polyhedron c δ) (x k)
  have hc:=poly_closed c δ
  have hv:=poly_convex c δ
  have hfreq : ∀ N,∃ k,N ≤ k ∧ good k := by
    apply frequent_minimum W good
    intro k hk
    have hh:=(hrun.2 k).2.2.2 hk
    refine ⟨hh.2.2.1,?_⟩
    intro heq
    dsimp [good]
    rw [heq]
    exact hh.2.2.2 heq
  have hmono : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hk : good k
    · have hs:=(hrun.2 k).2.2.1 hk
      have hi:=(projected_inner f (polyhedron c δ) (hrun.2 k).1 hc hv (α k) hs.1).1
      rw [←hs.2.1] at hi
      have hh:=mul_nonpos_of_nonneg_of_nonpos hμ₁.1.le hi
      linarith [hs.2.2.1]
    · exact ((hrun.2 k).2.2.2 hk).2.1
  apply finite_states_terminate (fun k => f (x k)) W good stop hfreq hmono
  · intro i j hi hj hij
    apply le_antisymm
    · apply hi.2
      rw [hij]
      exact hj.1
    · apply hj.2
      rw [←hij]
      exact hi.1
  · intro k hk hnot
    have hs:=(hrun.2 k).2.2.1 hk
    have hi:=(projected_inner f (polyhedron c δ) (hrun.2 k).1 hc hv (α k) hs.1).2 hnot
    rw [←hs.2.1] at hi
    have hh:=mul_neg_of_pos_of_neg hμ₁.1 hi
    linarith [hs.2.2.1]