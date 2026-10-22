-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_radial_interior_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T22:28:58.443784+00:00
-- url     : https://prove2.me/submissions/14840eb2-848f-466a-a2ef-6dc0469d326e

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_left_collision_point_in_negative_boundary
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_strict_radial_star_shaped
import Theorems.Thm_BirkhoffGlobalSection_first_ray_zero_in_left_negative_closure
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_position_radius_lt_one
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_radial_transversality
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

open BirkhoffGlobalSection Filter Topology Set

lemma lc_radial_hasDerivAt (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    HasDerivAt (fun a : ℝ => leviCivitaHamiltonian μ c (fun i : Fin 4 => a * s i))
      ((s 2 ^ 2 + s 3 ^ 2) + 2 * c * (s 0 ^ 2 + s 1 ^ 2)
        + 8 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * s 2)
        - 2 * μ * (s 0 * s 3 + s 1 * s 2)
        - 2 * μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s)
        + μ * (s 0 ^ 2 + s 1 ^ 2) * (8 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 - 4 * (s 0 ^ 2 - s 1 ^ 2)) /
          Real.sqrt (secondCollisionDistanceSq s) ^ 3) 1 := by
  have hx := hasDerivAt_id' (1 : ℝ)
  have e : ∀ i : Fin 4, HasDerivAt (fun a : ℝ => a * s i) (1 * s i) 1 := fun i => hx.mul_const (s i)
  have hin : HasDerivAt (fun a : ℝ => (2 * ((a * s 0) ^ 2 - (a * s 1) ^ 2) - 1) ^ 2 +
      (4 * (a * s 0) * (a * s 1)) ^ 2)
      (8 * (s 0 ^ 2 - s 1 ^ 2) * (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) + 64 * (s 0 * s 1) ^ 2) 1 := by
    have := ((((((e 0).fun_pow 2).fun_sub ((e 1).fun_pow 2)).const_mul 2).sub_const 1).fun_pow 2).fun_add
      ((((e 0).const_mul 4).fun_mul (e 1)).fun_pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hD' : (2 * ((1 * s 0) ^ 2 - (1 * s 1) ^ 2) - 1) ^ 2 + (4 * (1 * s 0) * (1 * s 1)) ^ 2 ≠ 0 := by
    simp only [one_mul]; exact hD.ne'
  have hS := hin.sqrt hD'
  simp only [one_mul] at hS
  unfold secondCollisionDistanceSq at hD ⊢
  have hNpos : 0 < Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) :=
    Real.sqrt_pos.2 hD
  have hsq : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 2 =
      (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 :=
    Real.sq_sqrt hD.le
  have hW := ((((e 2).fun_pow 2).fun_add ((e 3).fun_pow 2)).div_const 2)
  have hP := (((e 0).fun_pow 2).fun_add ((e 1).fun_pow 2))
  have hL := (((e 0).fun_mul (e 3)).fun_sub ((e 1).fun_mul (e 2)))
  have hM := (((e 0).fun_mul (e 3)).fun_add ((e 1).fun_mul (e 2)))
  have htot := ((((hW.fun_add (hP.const_mul c)).sub_const ((1 - μ) / 2)).fun_add
    ((hP.const_mul 2).fun_mul hL)).fun_sub (hM.const_mul μ)).fun_sub
    ((hP.const_mul μ).fun_div hS (by simpa using hNpos.ne'))
  refine htot.congr_deriv ?_
  simp only [one_mul]
  generalize hNdef : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) = N at *
  have hNne : N ≠ 0 := hNpos.ne'
  field_simp
  linear_combination (0:ℝ) * hsq


/-- A positive slope at `x` forces larger values just to the right. -/
lemma exists_right_gt (g : ℝ → ℝ) (x d b : ℝ) (hd : 0 < d) (hg : HasDerivAt g d x) (hb : x < b) :
    ∃ t ∈ Ioo x b, g x < g t := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hg).eventually (lt_mem_nhds hd)
  have h2 : ∀ᶠ t in 𝓝[>] x, 0 < slope g x t :=
    nhdsWithin_mono _ (fun t (ht : x < t) => (ne_of_gt ht)) h1
  have h3 : ∀ᶠ t in 𝓝[>] x, t ∈ Ioo x b := Ioo_mem_nhdsGT hb
  obtain ⟨t, ht1, ht2⟩ := (h2.and h3).exists
  refine ⟨t, ht2, ?_⟩
  rw [slope_def_field] at ht1
  have : 0 < t - x := by linarith [ht2.1]
  have := (div_pos_iff_of_pos_right this).1 ht1
  linarith

/-- A positive slope at `x` forces smaller values just to the left. -/
lemma exists_left_nbhd_lt (g : ℝ → ℝ) (x d : ℝ) (hd : 0 < d) (hg : HasDerivAt g d x) :
    ∃ l < x, ∀ t ∈ Ioo l x, g t < g x := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hg).eventually (lt_mem_nhds hd)
  have h2 : ∀ᶠ t in 𝓝[<] x, 0 < slope g x t :=
    nhdsWithin_mono _ (fun t (ht : t < x) => (ne_of_lt ht)) h1
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h2
  refine ⟨l, hl, fun t ht => ?_⟩
  have h := hsub ht
  simp only [mem_setOf_eq, slope_def_field] at h
  have : t - x < 0 := by linarith [ht.2]
  have := (div_pos_iff.1 h)
  rcases this with ⟨_, h'⟩ | ⟨h', _⟩
  · linarith
  · linarith

/-- If a function is negative at `0`, vanishes at `1`, and has positive derivative wherever
it is nonnegative, then it is negative on `[0,1)`. -/
lemma neg_before_first_zero (g : ℝ → ℝ) (hcont : ContinuousOn g (Icc 0 1))
    (h0 : g 0 < 0) (h1 : g 1 = 0)
    (hder : ∀ t ∈ Ioc (0:ℝ) 1, 0 ≤ g t → ∃ d, 0 < d ∧ HasDerivAt g d t) :
    ∀ t ∈ Ico (0:ℝ) 1, g t < 0 := by
  intro t0 ht0
  by_contra hcon
  push_neg at hcon
  have ht0pos : 0 < t0 := by
    rcases eq_or_lt_of_le ht0.1 with h | h
    · rw [← h] at hcon; linarith
    · exact h
  obtain ⟨d1, hd1, hg1⟩ := hder 1 ⟨by norm_num, le_rfl⟩ (by rw [h1])
  obtain ⟨l, hl, hleft⟩ := exists_left_nbhd_lt g 1 d1 hd1 hg1
  rw [h1] at hleft
  set m := max l t0 with hm
  have hm1 : m < 1 := max_lt hl ht0.2
  set S := {t ∈ Icc t0 m | 0 ≤ g t} with hS
  have hSsub : S ⊆ Icc t0 m := fun t ht => ht.1
  have hSclosed : IsClosed S := by
    have := ContinuousOn.preimage_isClosed_of_isClosed
      (hcont.mono (Icc_subset_Icc ht0.1 hm1.le)) isClosed_Icc (isClosed_Ici (a := (0:ℝ)))
    have e : S = Icc t0 m ∩ g ⁻¹' Ici 0 := by
      ext t; simp [hS, Set.mem_Icc]
    rw [e]; exact this
  have hSne : S.Nonempty := ⟨t0, ⟨⟨le_rfl, le_max_right _ _⟩, hcon⟩⟩
  have hScpt : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed hSsub
  set t1 := sSup S
  have ht1S : t1 ∈ S := hScpt.sSup_mem hSne
  have hbdd : BddAbove S := hScpt.bddAbove
  have ht1pos : 0 < t1 := lt_of_lt_of_le ht0pos ht1S.1.1
  have ht1m : t1 ≤ m := ht1S.1.2
  have hneg : ∀ t ∈ Ioo t1 1, g t < 0 := by
    intro t ht
    by_cases htm : t ≤ m
    · by_contra hc
      push_neg at hc
      have : t ∈ S := ⟨⟨by linarith [ht1S.1.1, ht.1], htm⟩, hc⟩
      have := le_csSup hbdd this
      linarith [ht.1]
    · push_neg at htm
      exact hleft t ⟨lt_of_le_of_lt (le_max_left _ _) htm, ht.2⟩
  obtain ⟨d, hd, hgd⟩ := hder t1 ⟨ht1pos, by linarith⟩ ht1S.2
  obtain ⟨t, ht, hgt⟩ := exists_right_gt g t1 d 1 hd hgd (by linarith)
  have := hneg t ht
  linarith [ht1S.2]

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x ∈ unitThreeSphere, ∀ R : ℝ,
      0 < R → (fun i : Fin 4 => R * x i) ∈ leftEnergyComponent μ c →
      ∀ r : ℝ, 0 < r → r < R →
        leviCivitaHamiltonian μ c (fun i : Fin 4 => r * x i) < 0 := by
  have hStar := left_negative_closure_strict_radial_star_shaped μ c hμ0 hμ1 hc
  have hTr := left_negative_closure_radial_transversality μ c hμ0 hμ1 hc
  obtain ⟨ρ0, hρ0, hrad⟩ := left_negative_closure_position_radius_lt_one μ c hμ0 hμ1 hc
  have hp := left_collision_point_in_negative_boundary μ c hμ0 hμ1
  set C : Set Phase := closure (connectedComponentIn
      {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧ 0 < secondCollisionDistanceSq u}
      (fun _ : Fin 4 => (0 : ℝ))) with hC
  -- the radial derivative at scale one
  set R1 : Phase → ℝ := fun s => (s 2 ^ 2 + s 3 ^ 2) + 2 * c * (s 0 ^ 2 + s 1 ^ 2)
        + 8 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * s 2)
        - 2 * μ * (s 0 * s 3 + s 1 * s 2)
        - 2 * μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s)
        + μ * (s 0 ^ 2 + s 1 ^ 2) * (8 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 - 4 * (s 0 ^ 2 - s 1 ^ 2)) /
          Real.sqrt (secondCollisionDistanceSq s) ^ 3 with hR1
  have hsc : ∀ (a : ℝ) (s : Phase), (fun i : Fin 4 => a * s i) = a • s := fun _ _ => rfl
  -- continuity
  have hDcont : Continuous secondCollisionDistanceSq := by
    unfold secondCollisionDistanceSq; fun_prop
  have hsqrt : ContinuousOn (fun s : Phase => Real.sqrt (secondCollisionDistanceSq s))
      {s | 0 < secondCollisionDistanceSq s} :=
    (Real.continuous_sqrt.comp hDcont).continuousOn
  have hsqrt_ne : ∀ s ∈ {s : Phase | 0 < secondCollisionDistanceSq s},
      Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := fun s hs => (Real.sqrt_pos.2 hs).ne'
  have hHcont : ContinuousOn (leviCivitaHamiltonian μ c)
      {s | 0 < secondCollisionDistanceSq s} := by
    unfold leviCivitaHamiltonian zNormSq wNormSq
    apply ContinuousOn.sub
    · exact Continuous.continuousOn (by fun_prop)
    · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop)) hsqrt hsqrt_ne
  have hR1cont : ContinuousOn R1 {s | 0 < secondCollisionDistanceSq s} := by
    rw [hR1]
    apply ContinuousOn.add
    · apply ContinuousOn.sub
      · exact Continuous.continuousOn (by fun_prop)
      · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop)) hsqrt hsqrt_ne
    · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop)) (hsqrt.pow 3)
        (fun s hs => pow_ne_zero 3 (hsqrt_ne s hs))
  have hDopen : IsOpen {s : Phase | 0 < secondCollisionDistanceSq s} :=
    isOpen_lt continuous_const hDcont
  set A : Set Phase := {s | 0 < secondCollisionDistanceSq s ∧
      (leviCivitaHamiltonian μ c s < 0 ∨ 0 < R1 s)} with hA
  have hAopen : IsOpen A := by
    have e : A = ({s | 0 < secondCollisionDistanceSq s} ∩ leviCivitaHamiltonian μ c ⁻¹' Iio 0) ∪
        ({s | 0 < secondCollisionDistanceSq s} ∩ R1 ⁻¹' Ioi 0) := by
      ext s; simp only [hA, mem_setOf_eq, mem_union, mem_inter_iff, mem_preimage, mem_Iio,
        mem_Ioi]; tauto
    rw [e]
    exact (hHcont.isOpen_inter_preimage hDopen isOpen_Iio).union
      (hR1cont.isOpen_inter_preimage hDopen isOpen_Ioi)
  set O : Set Phase := {y | ∀ t ∈ Icc (0 : ℝ) 1, t • y ∈ A} with hO
  have hOopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact (isCompact_Icc (a := (0 : ℝ)) (b := 1)).eventually_forall_of_forall_eventually
      (x₀ := y) (P := fun (y : Phase) (t : ℝ) => t • y ∈ A) (by
        intro t ht
        have hcont : Continuous (fun z : Phase × ℝ => z.2 • z.1) :=
          continuous_snd.smul continuous_fst
        exact hcont.continuousAt.preimage_mem_nhds (hAopen.mem_nhds (hy t ht)))
  -- the origin has negative energy
  have hD0 : secondCollisionDistanceSq (0 : Phase) = 1 := by
    simp [secondCollisionDistanceSq]
  have hH0 : leviCivitaHamiltonian μ c (0 : Phase) < 0 := by
    simp only [leviCivitaHamiltonian, hD0, zNormSq, wNormSq, Real.sqrt_one]
    simp
    linarith
  -- (a) zero-energy points of the closure lie in `O`
  have hZO : ∀ z ∈ C, leviCivitaHamiltonian μ c z = 0 → z ∈ O := by
    intro z hz hz0 t ht
    have hr := hrad z hz
    have hP : 4 * (z 0 ^ 2 + z 1 ^ 2) ^ 2 < 1 := by
      have e : ((leviCivitaPosition μ z) 0 + μ) ^ 2 + ((leviCivitaPosition μ z) 1) ^ 2 =
          4 * (z 0 ^ 2 + z 1 ^ 2) ^ 2 := by simp [leviCivitaPosition]; ring
      rw [e] at hr; linarith
    have hP2 : 2 * (z 0 ^ 2 + z 1 ^ 2) < 1 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have hDt : 0 < secondCollisionDistanceSq (t • z) := by
      have e : secondCollisionDistanceSq (t • z) =
          (1 - 2 * t ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ 2 + 8 * t ^ 2 * z 1 ^ 2 := by
        simp [secondCollisionDistanceSq]; ring
      rw [e]
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      have : 2 * t ^ 2 * (z 0 ^ 2 + z 1 ^ 2) < 1 := by
        nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg t]
      nlinarith [sq_nonneg (z 1), sq_nonneg t]
    refine ⟨hDt, ?_⟩
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · right
      rw [h1, one_smul]
      have hDz : 0 < secondCollisionDistanceSq z := by
        have := hDt; rwa [h1, one_smul] at this
      have hd := hTr z hz hz0
      rwa [(lc_radial_hasDerivAt μ c z hDz).deriv] at hd
    · left
      have := hStar z hz t ht.1 h1
      rwa [hsc] at this
  -- (b) zero-energy points of `O` lie in the closure
  have hOC : ∀ y ∈ O, leviCivitaHamiltonian μ c y = 0 → y ∈ C := by
    intro y hy hy0
    have hfree : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        0 < secondCollisionDistanceSq (fun i : Fin 4 => t * y i) := fun t h0 h1 =>
      (hy t ⟨h0, h1⟩).1
    set g : ℝ → ℝ := fun t => leviCivitaHamiltonian μ c (fun i : Fin 4 => t * y i) with hg
    have hgcont : ContinuousOn g (Icc 0 1) := by
      have hm : Continuous (fun t : ℝ => t • y) := continuous_id.smul continuous_const
      exact hHcont.comp hm.continuousOn (fun t ht => hfree t ht.1 ht.2)
    have hneg := neg_before_first_zero g hgcont
      (by simp only [hg, hsc, zero_smul]; exact hH0)
      (by simp only [hg, hsc, one_smul]; exact hy0)
      (by
        intro t ht hgt
        have hA' := hy t ⟨ht.1.le, ht.2⟩
        have hR : 0 < R1 (t • y) := by
          rcases hA'.2 with h | h
          · exfalso; simp only [hg, hsc] at hgt; linarith
          · exact h
        have hder := lc_radial_hasDerivAt μ c (t • y) hA'.1
        have htne : t ≠ 0 := ht.1.ne'
        have hdiv : HasDerivAt (fun u : ℝ => u / t) (1 / t) t := by
          simpa using (hasDerivAt_id t).div_const t
        have hder' : HasDerivAt
            (fun a : ℝ => leviCivitaHamiltonian μ c (fun i : Fin 4 => a * (t • y) i))
            (R1 (t • y)) (t / t) := by
          rw [div_self htne]; exact hder
        have hcomp := HasDerivAt.comp (h := fun u : ℝ => u / t) t hder' hdiv
        refine ⟨R1 (t • y) * (1 / t), mul_pos hR (one_div_pos.2 ht.1), ?_⟩
        have hfeq : g = (fun a : ℝ => leviCivitaHamiltonian μ c
            (fun i : Fin 4 => a * (t • y) i)) ∘ (fun u : ℝ => u / t) := by
          funext u
          simp only [hg, Function.comp]
          congr 1
          funext i
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
        rw [hfeq]; exact hcomp)
    have hnegative : ∀ t : ℝ, 0 ≤ t → t < 1 →
        leviCivitaHamiltonian μ c (fun i : Fin 4 => t * y i) < 0 :=
      fun t h0 h1 => hneg t ⟨h0, h1⟩
    have := first_ray_zero_in_left_negative_closure μ c hμ0 hμ1 y 1 one_pos hnegative hfree
    simpa using this
  -- the selected zero component lies in the closure
  have hsub : leftEnergyComponent μ c ⊆ C := by
    intro y hyL
    have hpre : IsPreconnected (leftEnergyComponent μ c) := isPreconnected_connectedComponentIn
    have hLE : leftEnergyComponent μ c ⊆ regularEnergyLocus μ c := connectedComponentIn_subset _ _
    have hsplit := isPreconnected_iff_subset_of_disjoint.1 hpre O Cᶜ hOopen
      isClosed_closure.isOpen_compl
      (by
        intro s hs
        by_cases hsC : s ∈ C
        · exact Or.inl (hZO s hsC (hLE hs).1)
        · exact Or.inr hsC)
      (by
        ext s
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
          not_not]
        intro hs hsO
        exact hOC s hsO (hLE hs).1)
    rcases hsplit with h | h
    · exact hOC y (h hyL) (hLE hyL).1
    · exfalso
      have hpL : leftCollisionPoint μ ∈ leftEnergyComponent μ c :=
        mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨y, hyL⟩)
      exact h hpL hp.1
  intro x _ R hR hy r hr hrR
  have hyC := hsub hy
  have := hStar _ hyC (r / R) (by positivity) ((div_lt_one hR).2 hrR)
  convert this using 2
  funext i
  field_simp
