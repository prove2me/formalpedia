-- Prove2me | solution 1 for FalconerPath.starting_pair_measures
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-11-03T20:24:21.100707+00:00
-- url     : https://prove2.me/submissions/39d4c787-e387-44ca-a295-dfaef7ffd903
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FalconerPath_defs
import Theorems.Thm_FalconerPath_starting_pair_projected_patches
import Theorems.Thm_FalconerPath_starting_pair_radial_pullback
import Theorems.Thm_FalconerPath_starting_pair_affine_model
import Theorems.Thm_FalconerPath_classical_distance_threshold
import Theorems.Thm_FalconerPath_coarse_exclusion_heavy_plates
import Theorems.Thm_FalconerPath_thin_tube_upgrade
import Theorems.Thm_FalconerPath_starting_pair_available_pullback
import Theorems.Thm_FalconerPath_starting_pair_coarse_partition
import Theorems.Thm_FalconerPath_integer_caps_and_lifting
import Theorems.Thm_FalconerPath_radial_lp
import Theorems.Thm_FalconerPath_finite_energy_and_projection
import Theorems.Thm_FalconerPath_simultaneous_projected_frostman
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-! Sketch of prep:starting-pairs, retaining the Stage 2 energy preparation. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000

namespace FalconerPath.StartingPairs

lemma probability_finite {n : ℕ} {μ : Measure (Space n)} (hμ : Probability μ) :
    FiniteBorel μ := by
  change μ univ < ∞
  rw [show μ univ = 1 from hμ]
  exact ENNReal.one_lt_top

/-- The initial probability from simultaneous projections really is compactly
supported in the original set, and its exponent is positive. -/
lemma initial_probability {d : ℕ} (hd : 2 ≤ d) (E : Set (Space d))
    (hE : IsCompact E) (hdim : (d:ℝ≥0∞)/2 < dimH E) :
    ∃ μ : Measure (Space d), Probability μ ∧ Carried μ E ∧
      IsCompact μ.support ∧ FiniteBorel μ ∧ ∃ s K : ℝ,
        (d:ℝ)/2 < s ∧ 0 < s ∧ 0 < K ∧ Frostman μ s K := by
  obtain ⟨μ, hμ, hcarried, s, K, hs, hK, hf⟩ :=
    (simultaneous_projected_frostman hd E hE hdim).1
  have hsupp : μ.support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed (mem_ae_iff.mpr hcarried)
  have hdreal : (2:ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨μ, hμ, hcarried, hE.of_isClosed_subset μ.isClosed_support hsupp,
    probability_finite hμ, s, K, hs, ?_, hK, hf⟩
  linarith only [hdreal, hs]

lemma restrict_frostman {n : ℕ} {μ : Measure (Space n)} {s K : ℝ}
    (hf : Frostman μ s K) (A : Set (Space n)) : Frostman (μ.restrict A) s K := by
  intro x r hr hδ hr1
  calc
    μ.restrict A (Metric.ball x r) = μ (Metric.ball x r ∩ A) :=
      Measure.restrict_apply measurableSet_ball
    _ ≤ μ (Metric.ball x r) := measure_mono inter_subset_left
    _ ≤ ENNReal.ofReal (K*r^s) := hf x r hr hδ hr1

lemma weaken_frostman {n : ℕ} {μ : Measure (Space n)} {s s' K : ℝ}
    (hf : Frostman μ s K) (hK : 0 ≤ K) (hs : s' ≤ s) : Frostman μ s' K := by
  intro x r hr hδ hr1
  exact (hf x r hr hδ hr1).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1 hs) hK))

/-- Choose epsilon after the common projected ball exponent. This supplies
exactly the finite energies needed for radial L^p, in both orientations. -/
lemma choose_radial_energies {h : ℕ} (hh : 1 ≤ h) (s K : ℝ)
    (hs : (h:ℝ) < s) (hK : 0 < K)
    (α β : Measure (Space (h+1))) (hα : Probability α) (hβ : Probability β)
    (hcα : IsCompact α.support) (hcβ : IsCompact β.support)
    (hfα : Frostman α s K) (hfβ : Frostman β s K) :
    ∃ ε : ℝ, 0 < ε ∧ ε < min (h:ℝ) 1 ∧
      energy ((h:ℝ)+ε) α < ∞ ∧ energy ((h:ℝ)+ε) β < ∞ := by
  have hhreal : (1:ℝ) ≤ h := by exact_mod_cast hh
  let a := min (s-(h:ℝ)) (min (h:ℝ) 1)
  have ha : 0 < a := lt_min (sub_pos.mpr hs) (lt_min (by linarith only [hhreal]) zero_lt_one)
  have ha₁ : a ≤ s-(h:ℝ) := min_le_left _ _
  have ha₂ : a ≤ min (h:ℝ) 1 := min_le_right _ _
  let ε := a/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεh : ε < min (h:ℝ) 1 := by dsimp [ε]; linarith only [ha, ha₂]
  have ht : 0 < (h:ℝ)+ε := by linarith only [hhreal, hε]
  have hts : (h:ℝ)+ε < s := by dsimp [ε]; linarith only [ha, ha₁]
  refine ⟨ε, hε, hεh, ?_, ?_⟩
  · exact (finite_energy_and_projection α (probability_finite hα) hcα.isBounded).1
      s K hK hfα ((h:ℝ)+ε) ht hts
  · exact (finite_energy_and_projection β (probability_finite hβ) hcβ.isBounded).1
      s K hK hfβ ((h:ℝ)+ε) ht hts

/-- The radial child can now be applied with one epsilon for both laws. -/
lemma prepare_radial {h : ℕ} (hh : 1 ≤ h) (s K : ℝ)
    (hs : (h:ℝ) < s) (hK : 0 < K)
    (α β : Measure (Space (h+1))) (hα : Probability α) (hβ : Probability β)
    (hcα : IsCompact α.support) (hcβ : IsCompact β.support)
    (hfα : Frostman α s K) (hfβ : Frostman β s K)
    (hsep : HasBoundedSeparated β α) :
    ∃ p : ℝ, 1 < p ∧ RadialLp β α p ∧
      ∃ Kα Kβ : Set (Space (h+1)), IsCompact Kα ∧ IsCompact Kβ ∧
        Kα ⊆ α.support ∧ Kβ ⊆ β.support ∧ 0 < α Kα ∧ 0 < β Kβ ∧
        ∃ L : ℝ, 0 < L ∧ UniformRadialLp
          (normalizedRestriction β Kβ) (normalizedRestriction α Kα) p L := by
  obtain ⟨ε, hε, hεh, hIα, hIβ⟩ :=
    choose_radial_energies hh s K hs hK α β hα hβ hcα hcβ hfα hfβ
  exact radial_lp hh ε hε hεh α β hα hβ hsep hIα hIβ

lemma probability_map {d m : ℕ} (P : Space d →L[ℝ] Space m)
    {μ : Measure (Space d)} (hμ : Probability μ) : Probability (Measure.map P μ) := by
  rw [Probability, Measure.map_apply P.measurable MeasurableSet.univ, preimage_univ]
  exact hμ

lemma radial_measurable {n : ℕ} (x : Space n) : Measurable (radial x) := by
  unfold radial
  fun_prop

lemma caps_subset {n : ℕ} (ν ρ : Measure (Space n)) {G H : PairSet n}
    (h : H ⊆ G) {q K δ : ℝ} (hc : bothCaps ν ρ G q K δ) : bothCaps ν ρ H q K δ := by
  constructor
  · filter_upwards [hc.1] with x hx
    have hm : forwardDirection ρ H x ≤ forwardDirection ρ G x := by
      apply Measure.map_mono _ (radial_measurable x)
      exact Measure.restrict_mono (show firstFiber H x ⊆ firstFiber G x from fun _ hz => h hz) le_rfl
    intro w hw u hu hδ hu1
    exact (hm _).trans (hx w hw u hu hδ hu1)
  · filter_upwards [hc.2] with y hy
    have hm : reverseDirection ν H y ≤ reverseDirection ν G y := by
      apply Measure.map_mono _ (radial_measurable y)
      exact Measure.restrict_mono (show secondFiber H y ⊆ secondFiber G y from fun _ hz => h hz) le_rfl
    intro w hw u hu hδ hu1
    exact (hm _).trans (hy w hw u hu hδ hu1)

/-- Intersect the exceptional sets with a Borel subrelation. -/
lemma available_subset {n : ℕ} {ν ρ : Measure (Space n)}
    {G H : ℕ → PairSet n} {q : ℝ} (hav : Available ν ρ G q)
    (hH : ∀ N, MeasurableSet (H N)) (hsub : ∀ N, H N ⊆ G N) : Available ν ρ H q := by
  intro e he
  obtain ⟨c, C, hc, hC, N₀, hN⟩ := hav e he
  refine ⟨c, C, hc, hC, N₀, ?_⟩
  intro N hNN
  obtain ⟨B, hB, hBG, hmass, hcap⟩ := hN N hNN
  refine ⟨H N ∩ B, (hH N).inter hB, inter_subset_left,
    (measure_mono inter_subset_right).trans hmass, caps_subset ν ρ ?_ hcap⟩
  intro z hz
  refine ⟨hsub N hz.1, ?_⟩
  intro hzB
  exact hz.2 ⟨hz.1, hzB⟩

lemma map_mem_support {d m : ℕ} (P : Space d →L[ℝ] Space m)
    (μ : Measure (Space d)) {x : Space d} (hx : x ∈ μ.support) :
    P x ∈ (Measure.map P μ).support := by
  rw [Measure.support_eq_forall_isOpen] at hx ⊢
  intro U hxU hU
  rw [Measure.map_apply P.measurable hU.measurableSet]
  exact hx (P ⁻¹' U) hxU (hU.preimage P.continuous)

/-- Lift the integer seed to the full supported product in the middle space. -/
lemma lift_full_available {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (P : Space d →L[ℝ] Space m) (hP : OrthogonalSurjection P)
    (ν ρ : Measure (Space d)) (hν : Probability ν) (hρ : Probability ρ)
    (hsep : HasBoundedSeparated ν ρ)
    (hprojsep : HasBoundedSeparated (Measure.map P ν) (Measure.map P ρ))
    (q : ℝ) (hq : 0 ≤ q)
    (hav : Available (Measure.map P ν) (Measure.map P ρ)
      (fun _ => (Measure.map P ν).support ×ˢ (Measure.map P ρ).support) q) :
    Available ν ρ (fun _ => ν.support ×ˢ ρ.support) q := by
  have hlift := starting_pair_available_pullback hm hmd P hP ν ρ hν hρ hsep hprojsep
    (fun _ => (Measure.map P ν).support ×ˢ (Measure.map P ρ).support)
    (fun _ => (Measure.isClosed_support.measurableSet).prod Measure.isClosed_support.measurableSet)
    q hq hav
  apply available_subset hlift (fun _ => ν.isClosed_support.measurableSet.prod ρ.isClosed_support.measurableSet)
  intro N z hz
  exact ⟨map_mem_support P ν hz.1, map_mem_support P ρ hz.2⟩

lemma integer_available {h : ℕ} (hh : 1 ≤ h) (ν ρ : Measure (Space (h+1)))
    (hν : Probability ν) (hρ : Probability ρ) (hsep : HasBoundedSeparated ν ρ)
    (p L : ℝ) (hp : 1 < p) (hL : 0 < L) (hlp : UniformRadialLp ν ρ p L) :
    Available ν ρ (fun _ => ν.support ×ˢ ρ.support) h := by
  intro e he
  obtain ⟨C, hC, N₀, hN⟩ := integer_caps_and_lifting.1 h hh ν ρ hν hρ hsep p L hp hL hlp e he
  refine ⟨e*(p-1)/2, C, by positivity, hC, N₀, ?_⟩
  intro N hNN
  obtain ⟨B, hB, hBG, hmass, hcap⟩ := hN N hNN
  refine ⟨B, hB, hBG, ?_, hcap⟩
  simpa only [show -e*(p-1)/2 = -(e*(p-1)/2) by ring] using hmass

lemma carried_mass {n : ℕ} (μ : Measure (Space n)) (hμ : Probability μ)
    (E : Set (Space n)) (hE : Carried μ E) : μ E = 1 := by
  have hm := measure_inter_conull (s := univ) hE
  rw [univ_inter] at hm
  exact hm.trans hμ

lemma one_piece {n : ℕ} (X Y : Set (Space n)) (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (b : ℝ) (hb : 1 ≤ b) : ProductPartition (X ×ˢ Y) b := by
  refine ⟨1, by simpa using hb, (fun _ => X), (fun _ => Y), (fun _ => ⟨hX, hY⟩), ?_, ?_⟩
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · ext z
    constructor
    · intro hz
      exact mem_iUnion.mpr ⟨(0 : Fin 1), hz⟩
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hi

/-- The integer seed is lifted first to the middle space. In odd dimension
it is restricted to the coarse filters before invoking the thin-tube child. -/
lemma geometry_filters {d h k : ℕ} {E : Set (Space d)} {r : ℝ}
    (hh : 1 ≤ h) (hparity : (d = 2*h ∧ k = h) ∨ (2 ≤ k ∧ d = 2*k-1 ∧ h+1 = k))
    (A : StartingGeometry d E r h k) (p L : ℝ) (hp : 1 < p) (hL : 0 < L)
    (hlp : UniformRadialLp (Measure.map A.Q (Measure.map A.P A.μ₁))
      (Measure.map A.Q (Measure.map A.P A.μ₂)) p L) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ω₀ ≤ 1 ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
      ∃ Γ : ℕ → PairSet d, PreparedFilters A.μ₁ A.μ₂ A.E₁ A.E₂ ω Γ := by
  have hmid₁ := probability_map A.P A.prob₁
  have hmid₂ := probability_map A.P A.prob₂
  have hsmall₁ := probability_map A.Q hmid₁
  have hsmall₂ := probability_map A.Q hmid₂
  have hseed := integer_available hh _ _ hsmall₁ hsmall₂ A.small_geometry p L hp hL hlp
  have havmid := lift_full_available (by omega) A.dimQ A.Q A.orthQ _ _ hmid₁ hmid₂
    A.middle_geometry A.small_geometry h (by positivity) hseed
  refine ⟨1, zero_lt_one, le_rfl, ?_⟩
  intro ω hω hω1
  rcases hparity with ⟨hd, hkh⟩ | ⟨hk, hd, hhk⟩
  · have hd' : (d:ℝ) = 2*h := by exact_mod_cast hd
    have hS : (d:ℝ)/2 = h := by linarith
    have hav := lift_full_available (by omega) A.dimP A.P A.orthP _ _ A.prob₁ A.prob₂
      A.geometry A.middle_geometry h (by positivity) havmid
    have hav' : Available A.μ₁ A.μ₂ (fun _ => A.E₁ ×ˢ A.E₂) ((d:ℝ)/2) := by
      simpa only [A.support₁, A.support₂, hS] using hav
    letI : IsProbabilityMeasure A.μ₁ := ⟨A.prob₁⟩
    letI : IsProbabilityMeasure A.μ₂ := ⟨A.prob₂⟩
    refine ⟨fun _ => A.E₁ ×ˢ A.E₂, ?_, ?_, ?_, ?_, hav'⟩
    · exact fun _ => ⟨A.compact₁.measurableSet.prod A.compact₂.measurableSet, Subset.rfl⟩
    · exact fun _ _ _ => Subset.rfl
    · simp only [iInter_const, Measure.prod_prod, carried_mass _ A.prob₁ _ A.carried₁,
        carried_mass _ A.prob₂ _ A.carried₂, mul_one]
      exact zero_lt_one
    · refine ⟨1, zero_lt_one, fun N => ?_⟩
      apply one_piece _ _ A.compact₁.measurableSet A.compact₂.measurableSet
      have hR : 1 ≤ scale N := one_le_pow₀ (by norm_num)
      simpa only [one_mul] using (Real.one_le_rpow hR (by positivity : 0 ≤ 2*(d:ℝ)*ω))
  · have hdadd : d+1 = 2*k := by omega
    have hdcast : (d:ℝ)+1 = 2*k := by exact_mod_cast hdadd
    have hS : (d:ℝ)/2 = (k:ℝ)-1/2 := by linarith
    have hhcast : (h:ℝ)+1 = k := by exact_mod_cast hhk
    let b := min A.χ (1/2:ℝ)
    let s := (d:ℝ)/2+b/2
    have hb : 0 < b := lt_min A.gap (by norm_num)
    have hbχ : b ≤ A.χ := min_le_left _ _
    have hbhalf : b ≤ 1/2 := min_le_right _ _
    have hs : (k:ℝ)-1/2 < s := by dsimp [s]; linarith
    have hsk : s < k := by dsimp [s]; linarith
    have hss : s ≤ (d:ℝ)/2+A.χ := by dsimp [s]; linarith
    have hf₁ := weaken_frostman A.middle_frostman₁ A.constant_pos.le hss
    have hf₂ := weaken_frostman A.middle_frostman₂ A.constant_pos.le hss
    obtain ⟨Γ, hΓ, hanti, hmass, hcells, ζ, C, hζ, hC, hplates⟩ :=
      coarse_exclusion_heavy_plates hk s A.C hs hsk A.constant_pos _ _ hmid₁ hmid₂
        A.middle_geometry hf₁ hf₂ (A.middle_zero hd) ω hω hω1
    have hbase : Available (Measure.map A.P A.μ₁) (Measure.map A.P A.μ₂) Γ ((k:ℝ)-1) := by
      have hav := available_subset havmid (fun N => (hΓ N).1) (fun N => (hΓ N).2)
      convert hav using 1 <;> linarith
    have hav := thin_tube_upgrade hk s A.C hs hsk A.constant_pos _ _ hmid₁ hmid₂
      A.middle_geometry hf₁ hf₂ Γ (fun N => (hΓ N).1) ζ C hζ hC hplates hbase
    have hkreal : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hnonneg : 0 ≤ (k:ℝ)-1/2 := by linarith
    have hlift := starting_pair_available_pullback (by omega) A.dimP A.P A.orthP _ _
      A.prob₁ A.prob₂ A.geometry A.middle_geometry Γ (fun N => (hΓ N).1)
      ((k:ℝ)-1/2) hnonneg hav
    obtain ⟨hmeas, hdec, hpos, hcount⟩ := starting_pair_coarse_partition A ω hω Γ hΓ hanti hmass hcells
    refine ⟨fun N => supportedPullback A.P A.E₁ A.E₂ (Γ N), hmeas, hdec, hpos, hcount, ?_⟩
    rw [hS]
    exact available_subset hlift (fun N => (hmeas N).1) (fun _ => inter_subset_right)

def to_starting_pair {d h k : ℕ} {E : Set (Space d)} {r : ℝ}
    (A : StartingGeometry d E r h k)
    (hf : ∃ ω₀ : ℝ, 0 < ω₀ ∧ ω₀ ≤ 1 ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
      ∃ Γ : ℕ → PairSet d, PreparedFilters A.μ₁ A.μ₂ A.E₁ A.E₂ ω Γ) : StartingPair d E r :=
  { E₁ := A.E₁, E₂ := A.E₂, μ₁ := A.μ₁, μ₂ := A.μ₂, χ := A.χ, C := A.C
    compact₁ := A.compact₁, compact₂ := A.compact₂, subset₁ := A.subset₁, subset₂ := A.subset₂
    prob₁ := A.prob₁, prob₂ := A.prob₂, carried₁ := A.carried₁, carried₂ := A.carried₂
    gap := A.gap, constant_pos := A.constant_pos, frostman₁ := A.frostman₁, frostman₂ := A.frostman₂
    separated := A.separated, patch := A.patch, filters := hf }

end FalconerPath.StartingPairs

open FalconerPath FalconerPath.StartingPairs

theorem solution {d : ℕ} (hd : 2 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E)
    (hdim : (d:ℝ≥0∞)/2 < dimH E) (patchRadius : ℝ) (hpatch : 0 < patchRadius) :
    0 < volume (distanceSet E) ∨ Nonempty (StartingPair d E patchRadius) := by
  classical
  obtain ⟨ρ, hρ, hcarried, hcρ, hfin, s, K, hs, hs0, hK, hf⟩ := initial_probability hd E hE hdim
  by_cases hzero : ∀ k : ℕ, 2 ≤ k → d = 2*k-1 → NoAffineMass ρ k
  · obtain ⟨h, k, hh, hparity, ⟨A⟩⟩ := starting_pair_projected_patches hd E hE hdim
      ρ hρ hcarried s K hs hK hf hzero patchRadius hpatch
    have hSh : (h:ℝ) ≤ (d:ℝ)/2 := by
      rcases hparity with ⟨hd, _⟩ | ⟨hk, hd, hhk⟩
      · have : (d:ℝ) = 2*h := by exact_mod_cast hd
        linarith
      · have hdadd : d+1 = 2*k := by omega
        have hd' : (d:ℝ)+1 = 2*k := by exact_mod_cast hdadd
        have hh' : (h:ℝ)+1 = k := by exact_mod_cast hhk
        linarith
    have hsmall₁ := probability_map A.Q (probability_map A.P A.prob₁)
    have hsmall₂ := probability_map A.Q (probability_map A.P A.prob₂)
    -- Lower the ball exponent to h+chi, so the chosen epsilon is also <chi.
    have hexp : (h:ℝ)+A.χ ≤ (d:ℝ)/2+A.χ := by linarith
    have hf₁ := weaken_frostman A.small_frostman₁ A.constant_pos.le hexp
    have hf₂ := weaken_frostman A.small_frostman₂ A.constant_pos.le hexp
    obtain ⟨p, hp, hlp, K₂, K₁, hc₂, hc₁, hs₂, hs₁, hm₂, hm₁, L, hL, huniform⟩ :=
      prepare_radial hh ((h:ℝ)+A.χ) A.C (by linarith [A.gap]) A.constant_pos _ _
        hsmall₂ hsmall₁ A.small_compact₂ A.small_compact₁ hf₂ hf₁ A.small_geometry
    obtain ⟨B, hBE₁, hBE₂, hBP, hBQ, hBχ, L', hL', hLp⟩ :=
      starting_pair_radial_pullback A p hp K₁ K₂ hc₁ hc₂ hs₁ hs₂ hm₁ hm₂ L hL huniform
    exact Or.inr ⟨to_starting_pair B (geometry_filters hh hparity B p L' hp hL' hLp)⟩
  · simp only [NoAffineMass] at hzero
    push_neg at hzero
    obtain ⟨k, hk, hdodd, V, hV, hVmass⟩ := hzero
    have hpos : 0 < ρ (V : Set _) := bot_lt_iff_ne_bot.mpr hVmass
    obtain ⟨η, hη, hcη, K', hK', hfη, hdist⟩ :=
      starting_pair_affine_model E hE ρ hρ hcarried s K hK hf V hV hpos
    have hdadd : d+1 = 2*k := by omega
    have hdcast : (d:ℝ)+1 = 2*k := by exact_mod_cast hdadd
    have hkcast : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hthreshold : ((k:ℝ)+1)/2 < s := by linarith
    exact Or.inl ((classical_distance_threshold hk η hη hcη s K' hthreshold hK' hfη).trans_le
      (measure_mono hdist))
