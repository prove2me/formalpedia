-- Prove2me | solution 1 for DbarRegularity.calderonZygmund_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:42:27.174704+00:00
-- url     : https://prove2.me/submissions/07340f98-dc65-40c4-8089-e6cc11562f6e

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_volume_closedCube
import Theorems.Thm_DbarRegularity_interior_closedCube
import Theorems.Thm_DbarRegularity_ae_tendsto_average_closedCube
import Theorems.Thm_DbarRegularity_dyadic_closedCube_subset



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem calderonZygmund_decomposition' {d : ℕ} (hd : 0 < d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (α : ℝ) (hα : 0 < α) :
    ∃ (F Ω : Set (EuclideanSpace ℝ (Fin d))) (ι : Type) (_ : Countable ι)
      (a : ι → EuclideanSpace ℝ (Fin d)) (s : ι → ℝ),
      F ∪ Ω = Set.univ ∧ Disjoint F Ω ∧
      (∀ᵐ x, x ∈ F → f x ≤ α) ∧
      Ω = ⋃ k, closedCube (a k) (s k) ∧
      (∀ k, 0 < s k) ∧
      Pairwise (fun k l => Disjoint (interior (closedCube (a k) (s k)))
        (interior (closedCube (a l) (s l)))) ∧
      ∀ k, α < (∫ x in closedCube (a k) (s k), f x) / (volume (closedCube (a k) (s k))).toReal ∧
        (∫ x in closedCube (a k) (s k), f x) / (volume (closedCube (a k) (s k))).toReal
          ≤ 2 ^ d * α := by
  classical
  -- the coarsest side length `L`, chosen with `∫ f ≤ α L^d`
  set L : ℝ := max 1 ((∫ x, f x) / α) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := by linarith
  have hLd : (∫ x, f x) ≤ α * L ^ d := by
    have h1 : (∫ x, f x) / α ≤ L := le_max_right _ _
    have h2 : L ≤ L ^ d := le_self_pow₀ hL1 (by omega)
    rw [div_le_iff₀ hα] at h1
    nlinarith
  have hf0' : 0 ≤ᵐ[volume] f := Eventually.of_forall hf0
  -- the grid of generation `n`
  set sd : ℕ → ℝ := fun n => L / 2 ^ n with hsd
  have hsd0 : ∀ n, 0 < sd n := fun n => by simp only [hsd]; positivity
  have hsd_succ : ∀ n, sd n = 2 * sd (n + 1) := fun n => by
    simp only [hsd, pow_succ]; field_simp
  have hsd_le : ∀ m n, m ≤ n → sd m = ((2 ^ (n - m) : ℕ) : ℝ) * sd n := by
    intro m n hmn
    have : (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
    simp only [hsd, this]; push_cast; field_simp
  set cor : ℕ → (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) :=
    fun n z => WithLp.toLp 2 fun i => (z i : ℝ) * sd n with hcor
  set Q : ℕ → (Fin d → ℤ) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun n z => closedCube (cor n z) (sd n) with hQ
  have hvol : ∀ n z, (volume (Q n z)).toReal = sd n ^ d := by
    intro n z
    simp only [hQ]
    rw [volume_closedCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal (hsd0 n).le]
  have hvolpos : ∀ n z, 0 < (volume (Q n z)).toReal := fun n z => by
    rw [hvol]; exact pow_pos (hsd0 n) d
  have hmeasQ : ∀ n z, MeasurableSet (Q n z) := by
    intro n z
    have : Q n z = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
        Icc (fun i => (z i : ℝ) * sd n) (fun i => (z i : ℝ) * sd n + sd n) := by
      ext x; simp [hQ, hcor, closedCube, Pi.le_def, forall_and]
    rw [this]
    exact measurableSet_Icc.preimage (PiLp.continuous_ofLp 2 _).measurable
  set avg : ℕ → (Fin d → ℤ) → ℝ :=
    fun n z => (∫ x in Q n z, f x) / (volume (Q n z)).toReal with havg
  -- the selected cubes: maximal grid cubes with average above `α`
  set sel : ℕ × (Fin d → ℤ) → Prop := fun p =>
    α < avg p.1 p.2 ∧ ∀ m < p.1, ∀ z, Q p.1 p.2 ⊆ Q m z → avg m z ≤ α with hsel
  -- generation `0` cubes have average at most `α`
  have havg0 : ∀ z, avg 0 z ≤ α := by
    intro z
    simp only [havg]
    rw [div_le_iff₀ (hvolpos 0 z), hvol]
    have : sd 0 = L := by simp [hsd]
    rw [this]
    exact (setIntegral_le_integral hf hf0').trans hLd
  -- the parent of a cube of generation `n + 1`
  have hparent : ∀ n z, Q (n + 1) z ⊆ Q n (fun i => z i / 2) := by
    intro n z x hx i
    have hx' := hx i
    simp only [hcor, PiLp.toLp_apply] at hx' ⊢
    have hz : z i / 2 * 2 ≤ z i ∧ z i + 1 ≤ (z i / 2 + 1) * 2 := by omega
    have h1 : ((z i / 2 : ℤ) : ℝ) * 2 ≤ z i := by exact_mod_cast hz.1
    have h2 : (z i : ℝ) + 1 ≤ (((z i / 2 : ℤ) : ℝ) + 1) * 2 := by exact_mod_cast hz.2
    have hs := hsd0 (n + 1)
    rw [hsd_succ n]
    have e1 := mul_le_mul_of_nonneg_right h1 hs.le
    have e2 := mul_le_mul_of_nonneg_right h2 hs.le
    constructor <;> nlinarith [hx'.1, hx'.2]
  -- grid cubes whose interiors meet are nested
  have hnest : ∀ n z m w, m ≤ n → (interior (Q n z) ∩ interior (Q m w)).Nonempty →
      Q n z ⊆ Q m w := by
    intro n z m w hmn hne
    exact dyadic_closedCube_subset (hsd0 n) (hsd_le m n hmn) z w hne
  -- the corner and the opposite corner lie in the cube
  have hcorner : ∀ n z, cor n z ∈ Q n z := fun n z i => by
    simp only [hcor, PiLp.toLp_apply]; constructor <;> linarith [hsd0 n]
  have hcorner' : ∀ n z, (WithLp.toLp 2 fun i => (z i : ℝ) * sd n + sd n) ∈ Q n z :=
    fun n z i => by simp only [hcor, PiLp.toLp_apply]; constructor <;> linarith [hsd0 n]
  -- same generation and nested: same index
  have hsame : ∀ n z w, Q n z ⊆ Q n w → z = w := by
    intro n z w hsub
    funext i
    have h1 := (hsub (hcorner n z) i).1
    have h2 := (hsub (hcorner' n z) i).2
    simp only [hcor, PiLp.toLp_apply] at h1 h2
    have hs := hsd0 n
    have a1 : (w i : ℝ) ≤ z i := le_of_mul_le_mul_right h1 hs
    have a2 : (z i : ℝ) ≤ w i := le_of_mul_le_mul_right (by linarith) hs
    exact_mod_cast le_antisymm a2 a1
  let ι := {p : ℕ × (Fin d → ℤ) // sel p}
  refine ⟨(⋃ k : ι, Q k.1.1 k.1.2)ᶜ, ⋃ k : ι, Q k.1.1 k.1.2, ι, inferInstance,
    fun k => cor k.1.1 k.1.2, fun k => sd k.1.1, compl_union_self _, disjoint_compl_left,
    ?_, rfl, fun k => hsd0 _, ?_, ?_⟩
  · -- `f ≤ α` almost everywhere off the selected cubes
    filter_upwards [ae_tendsto_average_closedCube hf.locallyIntegrable] with x hx hxF
    set kx : ℕ → Fin d → ℤ := fun n i => ⌊x i / sd n⌋ with hkx
    have hxQ : ∀ n, x ∈ Q n (kx n) := by
      intro n i
      simp only [hcor, hkx, PiLp.toLp_apply]
      have hs := hsd0 n
      have h1 := (le_div_iff₀ hs).1 (Int.floor_le (x i / sd n))
      have h2 := (div_lt_iff₀ hs).1 (Int.lt_floor_add_one (x i / sd n))
      constructor <;> nlinarith
    have hbound : ∀ n, avg n (kx n) ≤ α := by
      by_contra hcon
      push_neg at hcon
      have hex : ∃ n, α < avg n (kx n) := hcon
      set n0 := Nat.find hex with hn0
      have hsel0 : sel (n0, kx n0) := by
        refine ⟨Nat.find_spec hex, fun m hm w hsub => ?_⟩
        have hw : w = kx m := by
          funext i
          have h1 := (hsub (hcorner n0 (kx n0)) i).1
          have h2 := (hsub (hcorner' n0 (kx n0)) i).2
          simp only [hcor, PiLp.toLp_apply] at h1 h2
          have hxi := (hxQ n0 i).1
          have hs := hsd0 n0
          have hs' := hsd0 m
          have hlt := (div_lt_iff₀ hs).1 (Int.lt_floor_add_one (x i / sd n0))
          simp only [hcor, hkx, PiLp.toLp_apply] at hxi h1 h2
          rw [hkx]
          symm
          rw [Int.floor_eq_iff]
          constructor
          · rw [le_div_iff₀ hs']; linarith
          · rw [div_lt_iff₀ hs']; nlinarith
        rw [hw]
        exact not_lt.1 (Nat.find_min hex hm)
      exact hxF (mem_iUnion.2 ⟨⟨(n0, kx n0), hsel0⟩, hxQ n0⟩)
    have htend : Tendsto sd atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hsd0⟩
      simp only [hsd]
      exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hlim := hx (fun n => cor n (kx n)) sd htend (Eventually.of_forall hxQ)
    refine le_of_tendsto' hlim fun n => ?_
    have := hbound n
    simp only [havg] at this
    rw [setAverage_eq, smul_eq_mul, measureReal_def, inv_mul_eq_div]
    exact this
  · -- disjoint interiors
    rintro ⟨⟨n, z⟩, hz⟩ ⟨⟨m, w⟩, hw⟩ hne
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hint
    simp only at hint
    rcases lt_trichotomy m n with hmn | rfl | hmn
    · have hsub := hnest n z m w hmn.le hint
      exact absurd (hz.2 m hmn w hsub) (not_le.2 hw.1)
    · have hsub := hnest m z m w le_rfl hint
      have hzw := hsame m z w hsub
      subst hzw
      exact hne rfl
    · have hsub := hnest m w n z hmn.le (by rwa [Set.inter_comm])
      exact absurd (hw.2 n hmn z hsub) (not_le.2 hz.1)
  · -- the average bounds
    rintro ⟨⟨n, z⟩, hz⟩
    refine ⟨hz.1, ?_⟩
    show avg n z ≤ 2 ^ d * α
    rcases n with _ | n
    · exact absurd (havg0 z) (not_le.2 hz.1)
    · have hpar := hz.2 n (Nat.lt_succ_self n) _ (hparent n z)
      simp only [havg] at hpar ⊢
      rw [div_le_iff₀ (hvolpos _ _)] at hpar ⊢
      have hI : (∫ x in Q (n + 1) z, f x) ≤ ∫ x in Q n (fun i => z i / 2), f x :=
        setIntegral_mono_set hf.integrableOn (ae_restrict_of_ae hf0')
          (Eventually.of_forall (hparent n z))
      rw [hvol] at hpar ⊢
      rw [hsd_succ n, mul_pow] at hpar
      nlinarith

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution {d : ℕ} (hd : 0 < d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (α : ℝ) (hα : 0 < α) :
    ∃ (F Ω : Set (EuclideanSpace ℝ (Fin d))) (ι : Type) (_ : Countable ι)
      (a : ι → EuclideanSpace ℝ (Fin d)) (s : ι → ℝ),
      F ∪ Ω = Set.univ ∧ Disjoint F Ω ∧
      (∀ᵐ x, x ∈ F → f x ≤ α) ∧
      Ω = ⋃ k, closedCube (a k) (s k) ∧
      (∀ k, 0 < s k) ∧
      Pairwise (fun k l => Disjoint (interior (closedCube (a k) (s k)))
        (interior (closedCube (a l) (s l)))) ∧
      ∀ k, α < (∫ x in closedCube (a k) (s k), f x) / (volume (closedCube (a k) (s k))).toReal ∧
        (∫ x in closedCube (a k) (s k), f x) / (volume (closedCube (a k) (s k))).toReal
          ≤ 2 ^ d * α :=
  calderonZygmund_decomposition' hd f hf0 hf α hα
