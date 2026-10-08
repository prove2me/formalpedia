-- Prove2me | solution 1 for BellmanDP.Games.extended_min_max
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:55:03.226953+00:00
-- url     : https://prove2.me/submissions/63b22928-1243-4442-94c7-1a2eb5b86079

import Mathlib
import Definitions.Def_BellmanDP_Games_MinMax



namespace BellmanDP.Games

lemma emm_saddle {α β : Type*} (K : α → β → ℝ) (X : Set α) (Y : Set β) (ps : α) (qs : β)
    (hps : ps ∈ X) (hqs : qs ∈ Y) (hsad : ∀ q ∈ Y, ∀ p ∈ X, K p qs ≤ K ps q) :
    IsMaxMinMinMaxValue K X Y (K ps qs) := by
  refine ⟨⟨⟨ps, hps, ⟨qs, hqs, rfl⟩, ?_⟩, ?_⟩, ⟨⟨qs, hqs, ⟨ps, hps, rfl⟩, ?_⟩, ?_⟩⟩
  · rintro _ ⟨q, hq, rfl⟩; exact hsad q hq ps hps
  · rintro w ⟨x, hx, hw⟩
    exact (hw.2 ⟨qs, hqs, rfl⟩).trans (hsad qs hqs x hx)
  · rintro _ ⟨p, hp, rfl⟩; exact hsad qs hqs p hp
  · rintro w ⟨y, hy, hw⟩
    exact (hsad y hy ps hps).trans (hw.2 ⟨ps, hps, rfl⟩)

lemma emm_bilin_add_q {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (p : ι → ℝ)
    (q1 q2 : κ → ℝ) (a b : ℝ) :
    bilin A p (a • q1 + b • q2) = a * bilin A p q1 + b * bilin A p q2 := by
  simp only [bilin, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma emm_bilin_add_p {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (p1 p2 : ι → ℝ) (q : κ → ℝ) (a b : ℝ) :
    bilin A (a • p1 + b • p2) q = a * bilin A p1 q + b * bilin A p2 q := by
  simp only [bilin, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma emm_cont_q {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (p : ι → ℝ) :
    Continuous fun q : κ → ℝ => bilin A p q := by
  simp only [bilin]; fun_prop

lemma emm_cont_p {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (q : κ → ℝ) :
    Continuous fun p : ι → ℝ => bilin A p q := by
  simp only [bilin]; fun_prop

theorem emm_core {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A B : Matrix ι κ ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ ι, ∀ q ∈ stdSimplex ℝ κ, d ≤ bilin B p q) :
    ∃ v : ℝ, IsMaxMinMinMaxValue (fun p q => bilin A p q / bilin B p q)
      (stdSimplex ℝ ι) (stdSimplex ℝ κ) v := by
  classical
  set X := stdSimplex ℝ ι with hX
  set Y := stdSimplex ℝ κ with hY
  have neX : X.Nonempty := ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex ℝ _⟩
  have neY : Y.Nonempty := ⟨Pi.single (Classical.arbitrary κ) 1, single_mem_stdSimplex ℝ _⟩
  have hBpos : ∀ p ∈ X, ∀ q ∈ Y, 0 < bilin B p q := fun p hp q hq =>
    lt_of_lt_of_le hd (hB p hp q hq)
  let R : (κ → ℝ) → (ι → ℝ) → ℝ := fun q p => bilin A p q / bilin B p q
  have hfy : ∀ p ∈ X, LowerSemicontinuousOn (fun q => R q p) Y := by
    intro p hp
    refine ContinuousOn.lowerSemicontinuousOn ?_
    exact ((emm_cont_q A p).continuousOn).div ((emm_cont_q B p).continuousOn)
      fun q hq => (hBpos p hp q hq).ne'
  have hfx : ∀ q ∈ Y, UpperSemicontinuousOn (fun p => R q p) X := by
    intro q hq
    refine ContinuousOn.upperSemicontinuousOn ?_
    exact ((emm_cont_p A q).continuousOn).div ((emm_cont_p B q).continuousOn)
      fun p hp => (hBpos p hp q hq).ne'
  have hfy' : ∀ p ∈ X, QuasiconvexOn ℝ Y (fun q => R q p) := by
    intro p hp r
    intro q1 hq1 q2 hq2 a b ha hb hab
    obtain ⟨hq1Y, hq1r⟩ := hq1
    obtain ⟨hq2Y, hq2r⟩ := hq2
    have hY' : a • q1 + b • q2 ∈ Y := convex_stdSimplex ℝ _ hq1Y hq2Y ha hb hab
    refine ⟨hY', ?_⟩
    simp only [R] at hq1r hq2r ⊢
    rw [div_le_iff₀ (hBpos p hp q1 hq1Y)] at hq1r
    rw [div_le_iff₀ (hBpos p hp q2 hq2Y)] at hq2r
    rw [div_le_iff₀ (hBpos p hp _ hY'), emm_bilin_add_q, emm_bilin_add_q]
    nlinarith
  have hfx' : ∀ q ∈ Y, QuasiconcaveOn ℝ X (fun p => R q p) := by
    intro q hq r
    intro p1 hp1 p2 hp2 a b ha hb hab
    obtain ⟨hp1X, hp1r⟩ := hp1
    obtain ⟨hp2X, hp2r⟩ := hp2
    have hX' : a • p1 + b • p2 ∈ X := convex_stdSimplex ℝ _ hp1X hp2X ha hb hab
    refine ⟨hX', ?_⟩
    simp only [R] at hp1r hp2r ⊢
    rw [le_div_iff₀ (hBpos p1 hp1X q hq)] at hp1r
    rw [le_div_iff₀ (hBpos p2 hp2X q hq)] at hp2r
    rw [le_div_iff₀ (hBpos _ hX' q hq), emm_bilin_add_p, emm_bilin_add_p]
    nlinarith
  obtain ⟨qs, hqs, ps, hps, hsad⟩ := Sion.exists_isSaddlePointOn neY (convex_stdSimplex ℝ _)
    (isCompact_stdSimplex ℝ _) hfy hfy' (convex_stdSimplex ℝ _) neX (isCompact_stdSimplex ℝ _)
    hfx hfx'
  exact ⟨_, emm_saddle (fun p q => bilin A p q / bilin B p q) X Y ps qs hps hqs
    (fun q hq p hp => hsad q hq p hp)⟩

end BellmanDP.Games

open BellmanDP.Games


theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A B : Matrix ι κ ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ ι, ∀ q ∈ stdSimplex ℝ κ, d ≤ bilin B p q) :
    ∃ v : ℝ, IsMaxMinMinMaxValue (fun p q => bilin A p q / bilin B p q)
      (stdSimplex ℝ ι) (stdSimplex ℝ κ) v := by
  exact emm_core A B d hd hB
