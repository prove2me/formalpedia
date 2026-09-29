-- Prove2me | solution 1 for GPSAnalysis.Core.limit_point_properties
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:34:26.59924+00:00
-- url     : https://prove2.me/submissions/e5cacf00-4bc6-4d68-b70e-640cd8d49444

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

open Filter Topology

namespace GPSAnalysis.Core

theorem aux_lpp_step {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P) (k : ℕ) :
    P.fΩ (R.x (k + 1)) ≤ P.fΩ (R.x k) := by
  classical
  by_cases h : R.meshLocalOpt k
  · rw [(R.localOpt k h).2.1]
  · exact le_of_lt (R.improved k h).2.1

theorem aux_lpp_anti {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P) :
    Antitone (fun k => P.fΩ (R.x k)) :=
  antitone_nat_of_succ_le (fun k => aux_lpp_step P R k)

theorem aux_lpp_eq {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (k : ℕ) : P.f (R.x k) = P.fΩ (R.x k) := by
  classical
  have hlt : P.fΩ (R.x k) < ⊤ :=
    lt_of_le_of_lt (aux_lpp_anti P R (Nat.zero_le k)) hA1
  by_cases hmem : R.x k ∈ P.Ω
  · simp [GPSSetup.fΩ, barrier, hmem]
  · exfalso
    have : P.fΩ (R.x k) = ⊤ := by simp [GPSSetup.fΩ, barrier, hmem]
    rw [this] at hlt
    exact lt_irrefl _ hlt

theorem aux_lpp_fanti {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) : Antitone (fun k => P.f (R.x k)) := by
  intro i j hij
  simp only
  rw [aux_lpp_eq P R hA1 i, aux_lpp_eq P R hA1 j]
  exact aux_lpp_anti P R hij

theorem aux_lpp_ne_top {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (k : ℕ) : P.f (R.x k) ≠ ⊤ := by
  rw [aux_lpp_eq P R hA1 k]
  exact ne_of_lt (lt_of_le_of_lt (aux_lpp_anti P R (Nat.zero_le k)) hA1)

theorem aux_lpp_part2 {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) :
    ∀ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x → LowerSemicontinuousAt P.f xbar →
      ∃ ℓ : ℝ, Tendsto (fun k => P.f (R.x k)) atTop (𝓝 (ℓ : WithTop ℝ)) ∧
        P.f xbar ≤ (ℓ : WithTop ℝ) := by
  intro xbar hc hlsc
  have hanti := aux_lpp_fanti P R hA1
  -- every y < f xbar is below every f (x k)
  have key : ∀ y : WithTop ℝ, y < P.f xbar → ∀ k, y < P.f (R.x k) := by
    intro y hy k
    have hfr : ∃ᶠ j in atTop, y < P.f (R.x j) := hc.frequently (hlsc y hy)
    rw [frequently_atTop] at hfr
    obtain ⟨j, hj, hyj⟩ := hfr k
    exact lt_of_lt_of_le hyj (hanti hj)
  have hne : P.f xbar ≠ ⊤ := by
    intro htop
    have h0 : P.f (R.x 0) < P.f xbar := by
      rw [htop]; exact lt_top_iff_ne_top.2 (aux_lpp_ne_top P R hA1 0)
    exact lt_irrefl _ (key _ h0 0)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hne
  set a : ℕ → ℝ := fun k => (P.f (R.x k)).untop (aux_lpp_ne_top P R hA1 k) with ha_def
  have ha : ∀ k, ((a k : ℝ) : WithTop ℝ) = P.f (R.x k) := fun k => by
    simp [ha_def]
  have haanti : Antitone a := by
    intro i j hij
    have := hanti hij
    simp only at this
    rw [← ha i, ← ha j] at this
    exact WithTop.coe_le_coe.1 this
  have hba : ∀ k, b ≤ a k := by
    intro k
    apply le_of_forall_lt
    intro c hc
    have h1 : ((c : ℝ) : WithTop ℝ) < P.f xbar := by
      rw [← hb]; exact WithTop.coe_lt_coe.2 hc
    have h2 := key _ h1 k
    rw [← ha k] at h2
    exact WithTop.coe_lt_coe.1 h2
  have hbdd : BddBelow (Set.range a) := ⟨b, by rintro _ ⟨k, rfl⟩; exact hba k⟩
  refine ⟨⨅ k, a k, ?_, ?_⟩
  · have ht : Tendsto a atTop (𝓝 (⨅ k, a k)) := tendsto_atTop_ciInf haanti hbdd
    have ht2 := (WithTop.continuous_coe.tendsto (⨅ k, a k)).comp ht
    have hfun : (fun k => P.f (R.x k)) = ((↑) : ℝ → WithTop ℝ) ∘ a := by
      funext k; simp [ha k]
    rw [hfun]; exact ht2
  · rw [← hb]
    exact WithTop.coe_le_coe.2 (le_ciInf hba)

end GPSAnalysis.Core

open GPSAnalysis.Core
open Filter Topology

theorem solution {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R) :
    (∃ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x) ∧
    (∀ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x → LowerSemicontinuousAt P.f xbar →
      ∃ ℓ : ℝ, Tendsto (fun k => P.f (R.x k)) atTop (𝓝 (ℓ : WithTop ℝ)) ∧
        P.f xbar ≤ (ℓ : WithTop ℝ)) ∧
    ((∀ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x → ContinuousAt P.f xbar) →
      ∀ x₁ x₂ : Fin n → ℝ, MapClusterPt x₁ atTop R.x → MapClusterPt x₂ atTop R.x →
        P.f x₁ = P.f x₂) := by
  refine ⟨?_, aux_lpp_part2 P R hA1, ?_⟩
  · obtain ⟨X, hX, hmem⟩ := hA3
    obtain ⟨z, -, hz⟩ := hX.exists_mapClusterPt (f := atTop) (u := R.x)
      (tendsto_principal.2 (Eventually.of_forall hmem))
    exact ⟨z, hz⟩
  · intro hcont x₁ x₂ h₁ h₂
    obtain ⟨ℓ, hℓ, -⟩ := aux_lpp_part2 P R hA1 x₁ h₁ (hcont x₁ h₁).lowerSemicontinuousAt
    have hval : ∀ x : Fin n → ℝ, MapClusterPt x atTop R.x → P.f x = (ℓ : WithTop ℝ) := by
      intro x hx
      have hmc : MapClusterPt (P.f x) atTop (P.f ∘ R.x) := hx.continuousAt_comp (hcont x hx)
      apply eq_of_nhds_neBot
      have : NeBot (𝓝 (P.f x) ⊓ map (P.f ∘ R.x) atTop) := hmc
      exact this.mono (inf_le_inf_left _ hℓ)
    rw [hval x₁ h₁, hval x₂ h₂]
