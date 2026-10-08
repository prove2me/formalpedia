-- Prove2me | solution 1 for BregmanRelax.Remotest.lemma2_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:38:13.338681+00:00
-- url     : https://prove2.me/submissions/554dfa8c-49e5-4c23-8abf-70c416a4af5b

import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions



namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem breg_three_point {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (j : ι) (y : X) (hy : y ∈ S)
    (z : X) (hz : z ∈ A j ∩ S) :
    D (P j y) y + D z (P j y) ≤ D z y := by
  obtain ⟨hPmem, hPmin⟩ := hA.proj j y hy
  have hconv := hA.convexOn j y hy
  have hPP : D (P j y) (P j y) = 0 := (hA.eq_zero_iff _ hPmem.2 _ hPmem.2).2 rfl
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      D (P j y) y - D (P j y + t • (z - P j y)) (P j y) / t ≤ D z y - D z (P j y) := by
    intro t ht0 ht1
    have hw : (1 - t) • P j y + t • z = P j y + t • (z - P j y) := by
      rw [sub_smul, smul_sub, one_smul]; abel
    have h1 := hconv.2 hPmem hz (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    rw [hw] at h1
    have hwmem : P j y + t • (z - P j y) ∈ A j ∩ S := by
      rw [← hw]; exact hconv.1 hPmem hz (by linarith) ht0.le (by ring)
    have h2 := hPmin _ hwmem
    simp only [smul_eq_mul, hPP, sub_zero] at h1
    have h3 : t * D (P j y) y - D (P j y + t • (z - P j y)) (P j y)
        ≤ t * (D z y - D z (P j y)) := by nlinarith
    have : D (P j y) y - D (P j y + t • (z - P j y)) (P j y) / t
        = (t * D (P j y) y - D (P j y + t • (z - P j y)) (P j y)) / t := by
      field_simp
    rw [this, div_le_iff₀ ht0]; linarith
  have hlim : Filter.Tendsto (fun t : ℝ => D (P j y) y - D (P j y + t • (z - P j y)) (P j y) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (D (P j y) y - 0)) :=
    tendsto_const_nhds.sub (hA.deriv_zero _ hPmem.2 z hz.2)
  rw [sub_zero] at hlim
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      D (P j y) y - D (P j y + t • (z - P j y)) (P j y) / t ≤ D z y - D z (P j y) := by
    have : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with t ht using key t ht.1 ht.2
  have := le_of_tendsto hlim hev
  linarith


theorem breg_memS {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) : ∀ n, x n ∈ S := by
  intro n
  induction n with
  | zero => exact hx.1
  | succ n ih => rw [hx.2 n]; exact (hA.proj _ _ ih).1.2

theorem breg_desc {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (z : X) (hz : z ∈ (⋂ j, A j) ∩ S) (n : ℕ) :
    D (x (n + 1)) (x n) + D z (x (n + 1)) ≤ D z (x n) := by
  rw [hx.2 n]
  exact breg_three_point hA (i n) (x n) (breg_memS hA i x hx n) z
    ⟨Set.mem_iInter.1 hz.1 _, hz.2⟩

theorem breg_anti {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (z : X) (hz : z ∈ (⋂ j, A j) ∩ S) : Antitone (fun n => D z (x n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h1 := breg_desc hA i x hx z hz n
  have h2 := hA.nonneg _ (breg_memS hA i x hx (n+1)) _ (breg_memS hA i x hx n)
  linarith

theorem lemma2_limit_core {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (z : X) (hz : z ∈ (⋂ j, A j) ∩ S) :
    ∃ c : ℝ, Filter.Tendsto (fun n => D z (x n)) Filter.atTop (nhds c) := by
  refine ⟨_, tendsto_atTop_ciInf (breg_anti hA i x hx z hz) ?_⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact hA.nonneg _ hz.2 _ (breg_memS hA i x hx n)

theorem lemma2_step_core {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) :
    Filter.Tendsto (fun n => D (x (n + 1)) (x n)) Filter.atTop (nhds 0) := by
  obtain ⟨z, hzS, hzR⟩ := hR
  have hz : z ∈ (⋂ j, A j) ∩ S := ⟨hzR, hzS⟩
  obtain ⟨c, hc⟩ := lemma2_limit_core hA i x hx z hz
  have h2 : Filter.Tendsto (fun n => D z (x n) - D z (x (n + 1))) Filter.atTop (nhds (c - c)) :=
    hc.sub (hc.comp (Filter.tendsto_add_atTop_nat 1))
  rw [sub_self] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 ?_ ?_
  · intro n
    exact hA.nonneg _ (breg_memS hA i x hx (n+1)) _ (breg_memS hA i x hx n)
  · intro n
    have := breg_desc hA i x hx z hz n
    show D (x (n + 1)) (x n) ≤ D z (x n) - D z (x (n + 1))
    linarith

theorem lemma2_compact_core {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ}
    {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : BregmanRelax.Cyclic.CondV S D ((⋂ j, A j) ∩ S))
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) :
    ∃ K : Set X, IsSeqCompact K ∧ ∀ n, x n ∈ K := by
  obtain ⟨z, hzS, hzR⟩ := hR
  have hz : z ∈ (⋂ j, A j) ∩ S := ⟨hzR, hzS⟩
  refine ⟨_, hV z hz (D z (x 0)), fun n => ⟨breg_memS hA i x hx n, ?_⟩⟩
  exact breg_anti hA i x hx z hz (Nat.zero_le n)

theorem theorem2_core {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : BregmanRelax.Cyclic.CondV S D ((⋂ j, A j) ∩ S))
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (hi : IsRemotestControl D P i x)
    (x' : X) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds x')) :
    x' ∈ ⋂ j, A j := by
  have hS := breg_memS hA i x hx
  obtain ⟨z, hzS, hzR⟩ := hR
  have hz : z ∈ (⋂ j, A j) ∩ S := ⟨hzR, hzS⟩
  have hstep := lemma2_step_core hA ⟨z, hzS, hzR⟩ i x hx
  have hcl : x' ∈ closure S :=
    mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => hS (φ k))
  rw [Set.mem_iInter]
  intro j
  have hPmem : ∀ k, P j (x (φ k)) ∈ A j ∩ S := fun k => (hA.proj j _ (hS (φ k))).1
  have hD : Filter.Tendsto (fun k => D (P j (x (φ k))) (x (φ k))) Filter.atTop (nhds 0) := by
    have hs2 : Filter.Tendsto (fun k => D (x (φ k + 1)) (x (φ k))) Filter.atTop (nhds 0) :=
      hstep.comp hφ.tendsto_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs2 ?_ ?_
    · intro k; exact hA.nonneg _ (hPmem k).2 _ (hS (φ k))
    · intro k
      show D (P j (x (φ k))) (x (φ k)) ≤ D (x (φ k + 1)) (x (φ k))
      rw [hx.2 (φ k)]; exact hi (φ k) j
  have hK : ∃ K : Set X, IsSeqCompact K ∧ ∀ k, P j (x (φ k)) ∈ K := by
    refine ⟨_, hV z hz (D z (x 0)), fun k => ⟨(hPmem k).2, ?_⟩⟩
    have h1 := breg_three_point hA j (x (φ k)) (hS (φ k)) z ⟨Set.mem_iInter.1 hzR j, hzS⟩
    have h2 := hA.nonneg _ (hPmem k).2 _ (hS (φ k))
    have h3 := breg_anti hA i x hx z hz (Nat.zero_le (φ k))
    show D z (P j (x (φ k))) ≤ D z (x 0)
    simp only at h3
    linarith
  have hconv := hA.conv (fun k => P j (x (φ k))) (fun k => x (φ k)) x'
    (fun k => (hPmem k).2) (fun k => hS (φ k)) hD hlim hcl hK
  exact (hA.isClosed j).mem_of_tendsto hconv (Filter.Eventually.of_forall fun k => (hPmem k).1)

end BregmanRelax.Remotest

open BregmanRelax.Remotest
open BregmanRelax.Remotest
variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem solution {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) :
    Filter.Tendsto (fun n => D (x (n + 1)) (x n)) Filter.atTop (nhds 0) := by
  exact lemma2_step_core hA hR i x hx
