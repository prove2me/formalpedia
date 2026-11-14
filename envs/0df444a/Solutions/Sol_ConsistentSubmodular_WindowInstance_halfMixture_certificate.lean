-- Prove2me | solution 1 for ConsistentSubmodular.WindowInstance.halfMixture_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:29.909426+00:00
-- url     : https://prove2.me/submissions/9bdaa69b-9153-47a8-80a5-ff61be5c31cd

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate
import Theorems.Thm_ConsistentSubmodular_WindowInstance_pair_submodular
import Theorems.Thm_ConsistentSubmodular_WindowInstance_pairValue_le
import Theorems.Thm_ConsistentSubmodular_WindowInstance_prefix_bound
import Theorems.Thm_ConsistentSubmodular_WindowInstance_halfMixture_suffix

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

theorem mix_mix_left (p q : Point m) (x y : ℝ) :
    mix (mix p q x) p y = mix p q ((1 - y) * x) := by
  funext i
  simp only [mix]
  ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem benchmark_nonneg (j : Fin (W.lastStage + 1)) : 0 ≤ W.benchmark j :=
  W.objective.nonnegative _

theorem pair_union_ge (j a b : Fin (W.lastStage + 1)) :
    W.objective.value (W.arrivals j ∪ W.candidate a) ≤
        W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) ∧
      W.objective.value (W.arrivals j ∪ W.candidate b) ≤
        W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) := by
  constructor <;> apply W.objective.monotone <;> intro e he <;>
    simp only [Finset.mem_union] at he ⊢ <;> tauto

end WindowInstance

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace PolygonalPath

variable {m : ℕ}

theorem along_segment {Φ : Point m → Prop} {p q : Point m}
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Φ (mix p q x)) : (segment p q).Along Φ := by
  constructor
  · intro j
    fin_cases j
    · simpa [segment] using h 0 le_rfl zero_le_one
    · simpa [segment] using h 1 zero_le_one le_rfl
  · intro j x hx hx1
    fin_cases j
    simpa [segment] using h x hx hx1

theorem along_twoSegments {Φ : Point m → Prop} {p q r : Point m}
    (h1 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Φ (mix p q x))
    (h2 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Φ (mix q r x)) : (twoSegments p q r).Along Φ := by
  constructor
  · intro j
    fin_cases j
    · simpa [twoSegments] using h1 0 le_rfl zero_le_one
    · simpa [twoSegments] using h1 1 zero_le_one le_rfl
    · simpa [twoSegments] using h2 1 zero_le_one le_rfl
  · intro j x hx hx1
    fin_cases j
    · simpa [twoSegments] using h1 x hx hx1
    · simpa [twoSegments] using h2 x hx hx1

end PolygonalPath

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- `r_j ≤ g_j`, by the optimality of `O_j`. -/
theorem residual_le_gain (i j : Fin (W.lastStage + 1)) : W.residual i j ≤ W.gain j := by
  have h := W.candidate_optimal j (W.candidate i) (W.candidate_subset i) (W.candidate_card i)
  rw [Finset.union_comm (W.candidate i)] at h
  unfold residual gain benchmark
  linarith

theorem residual_self (j : Fin (W.lastStage + 1)) : W.residual j j = W.gain j := by
  simp [residual, gain, benchmark, Finset.union_comm]

/-- Moving from the midpoint toward the endpoint of larger residual does not
decrease the two-type value: by (23), its derivative is the endpoint difference
plus `(2s - 1) o`. -/
theorem pairValue_half_le (j a b : Fin (W.lastStage + 1)) (s : ℝ)
    (hs : 0 ≤ (s - 1 / 2) * (W.residual b j - W.residual a j)) :
    W.pairValue j a b (1 / 2) ≤ W.pairValue j a b s := by
  have ho := W.pair_submodular j a b
  have hsq := sq_nonneg (s - 1 / 2)
  unfold residual at hs
  unfold pairValue twoTypeValue
  nlinarith [mul_nonneg hsq (show 0 ≤ W.objective.value (W.arrivals j ∪ W.candidate a) +
    W.objective.value (W.arrivals j ∪ W.candidate b) -
    W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) -
    W.objective.value (W.arrivals j) by linarith)]

/-- The midpoint bound (24) at stage `j`, with
`(u + z)/2 - min(u, z)/4 = (u + z + max(u, z))/4`: four times
`H_{R_j}(O_0, O_c; 1/2)` is at least `4 L_j`. -/
theorem half_pair_lower (j c : Fin (W.lastStage + 1)) :
    4 * W.arrivalValue j + W.residual 0 j + W.residual c j +
        max (W.residual 0 j) (W.residual c j) ≤ 4 * W.pairValue j 0 c (1 / 2) := by
  obtain ⟨h0, hc⟩ := W.pair_union_ge j 0 c
  unfold residual arrivalValue pairValue twoTypeValue
  rcases le_total (W.objective.value (W.arrivals j ∪ W.candidate 0))
    (W.objective.value (W.arrivals j ∪ W.candidate c)) with h | h
  · rw [max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith

/-- The second exit edge, toward the terminal optimizer `O_m`, keeps
`λ_m + 3v/4`, where `v` is the terminal residual of its starting candidate. -/
theorem pairValue_terminal (b : Fin (W.lastStage + 1)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    W.arrivalValue (Fin.last W.lastStage) + 3 / 4 * W.residual b (Fin.last W.lastStage) ≤
      W.pairValue (Fin.last W.lastStage) b (Fin.last W.lastStage) s := by
  have hopt := W.candidate_optimal (Fin.last W.lastStage) (W.candidate b)
    (W.candidate_subset b) (W.candidate_card b)
  rw [Finset.union_comm (W.candidate b), Finset.union_comm (W.candidate _)] at hopt
  obtain ⟨hm, -⟩ := W.pair_union_ge (Fin.last W.lastStage) b (Fin.last W.lastStage)
  have hb := W.objective.monotone (W.arrivals (Fin.last W.lastStage))
    (W.arrivals (Fin.last W.lastStage) ∪ W.candidate b) Finset.subset_union_left
  have hq : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hq0 : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
  unfold residual arrivalValue pairValue twoTypeValue
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hb)]

end WindowInstance

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem envelopeTerm_le_envelope (β : ℝ) (j : Fin (W.lastStage + 1)) :
    W.envelopeTerm β j ≤ W.envelope β :=
  Finset.le_sup' _ (Finset.mem_univ j)

/-- The requirement behind the envelope: at every stage `j`,
`4 β P_j ≤ 4 λ_j + 2 r_j + K_c` once `K_c ≥ D`. -/
theorem envelope_requirement {β : ℝ} {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) (j : Fin (W.lastStage + 1)) :
    4 * β * W.benchmark j ≤ 4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c := by
  have hm := W.envelopeTerm_le_envelope β j
  simp only [envelopeTerm, credit, gain] at hm hDc ⊢
  linarith

/-- Persistence on the prefix (Theorem B.4): for `j ≤ c`, Lemma B.5 and the
envelope give `H_{R_j}(O_0, O_c; 1/2) ≥ β P_j`. -/
theorem halfMixture_prefix {β : ℝ} {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) {j : Fin (W.lastStage + 1)} (hjc : j ≤ c) :
    β * W.benchmark j ≤ W.pairValue j 0 c (1 / 2) := by
  have hb := W.prefix_bound hjc
  have := W.envelope_requirement hDc j
  linarith

end WindowInstance

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem solution {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hαβ : α ≤ β) (hα : 2 * β * α ≤ 1) {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) (hafter : ∀ j, c < j → W.credit j < W.envelope β) :
    ∃ Z : W.Certificate α 3, Z.anchor = mix (vertex 0) (vertex c) (1 / 2) ∧
      Z.entry.pieces = 1 ∧ Z.exit.pieces = 2 := by
  classical
  have hprefix (j : Fin (W.lastStage + 1)) (hjc : j ≤ c) :
      β * W.benchmark j ≤ W.pairValue j 0 c (1 / 2) := W.halfMixture_prefix hDc hjc
  have hsuffix (j : Fin (W.lastStage + 1)) (hcj : c < j) :
      α * W.benchmark j ≤ W.arrivalValue j +
        (W.residual 0 j + W.residual c j + max (W.residual 0 j) (W.residual c j)) / 4 :=
    W.halfMixture_suffix hβ hβ' hα hafter hcj
  -- The anchor and its persistence.
  let p : Point W.lastStage := mix (vertex 0) (vertex c) (1 / 2)
  have hp : IsSimplex p := (simplex_vertex 0).mix (simplex_vertex c) (by norm_num) (by norm_num)
  have hpersist (j : Fin (W.lastStage + 1)) : α * W.benchmark j ≤ W.mixtureValue j p := by
    have hpair := W.pairValue_le j 0 c (s := 1 / 2) (by norm_num) (by norm_num)
    rcases le_or_gt j c with hjc | hcj
    · have hb := hprefix j hjc
      have hPj := W.benchmark_nonneg j
      nlinarith [mul_le_mul_of_nonneg_right hαβ hPj]
    · have hl := W.half_pair_lower j c
      have hs := hsuffix j hcj
      linarith
  -- The exit reserve `L_m ≥ α P_m` at the terminal stage.
  have hreserve : α * W.benchmark (Fin.last W.lastStage) ≤
      W.arrivalValue (Fin.last W.lastStage) +
        (W.residual 0 (Fin.last W.lastStage) + W.residual c (Fin.last W.lastStage) +
          max (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))) / 4 := by
    rcases lt_or_eq_of_le (Fin.le_last c) with hcl | hcl
    · exact hsuffix _ hcl
    · have hb := W.envelope_requirement hDc (Fin.last W.lastStage)
      rw [hcl] at hb ⊢
      rw [residual_self]
      have hug := W.residual_le_gain 0 (Fin.last W.lastStage)
      rw [max_eq_right hug]
      have hPm := W.benchmark_nonneg (Fin.last W.lastStage)
      unfold credit at hb
      nlinarith [mul_le_mul_of_nonneg_right hαβ hPm]
  have hmid := W.half_pair_lower (Fin.last W.lastStage) c
  -- The exit partner: the endpoint with larger terminal residual.
  obtain ⟨b, hbres, hbside⟩ : ∃ b : Fin (W.lastStage + 1),
      W.residual b (Fin.last W.lastStage) =
        max (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage)) ∧
      ((b = c ∧ W.residual 0 (Fin.last W.lastStage) ≤ W.residual c (Fin.last W.lastStage)) ∨
        (b = 0 ∧ W.residual c (Fin.last W.lastStage) ≤ W.residual 0 (Fin.last W.lastStage))) := by
    rcases le_total (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))
      with huz | hzu
    · exact ⟨c, (max_eq_right huz).symm, Or.inl ⟨rfl, huz⟩⟩
    · exact ⟨0, (max_eq_left hzu).symm, Or.inr ⟨rfl, hzu⟩⟩
  have hexit1 (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
      α * W.benchmark (Fin.last W.lastStage) ≤
        W.mixtureValue (Fin.last W.lastStage) (mix p (vertex b) x) := by
    rcases hbside with ⟨hbc, huz⟩ | ⟨hb0, hzu⟩
    · have hmixeq : mix p (vertex b) x = mix (vertex 0) (vertex c) ((1 - x) * (1 / 2) + x) := by
        rw [hbc]
        exact mix_mix_right _ _ _ _
      rw [hmixeq]
      have hpair := W.pairValue_le (Fin.last W.lastStage) 0 c
        (s := (1 - x) * (1 / 2) + x) (by nlinarith) (by nlinarith)
      have hmono := W.pairValue_half_le (Fin.last W.lastStage) 0 c ((1 - x) * (1 / 2) + x)
        (by nlinarith)
      linarith
    · have hmixeq : mix p (vertex b) x = mix (vertex 0) (vertex c) ((1 - x) * (1 / 2)) := by
        rw [hb0]
        exact mix_mix_left _ _ _ _
      rw [hmixeq]
      have hpair := W.pairValue_le (Fin.last W.lastStage) 0 c
        (s := (1 - x) * (1 / 2)) (by nlinarith) (by nlinarith)
      have hmono := W.pairValue_half_le (Fin.last W.lastStage) 0 c ((1 - x) * (1 / 2))
        (by nlinarith)
      linarith
  have hexit2 (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
      α * W.benchmark (Fin.last W.lastStage) ≤
        W.mixtureValue (Fin.last W.lastStage) (mix (vertex b) (vertex (Fin.last W.lastStage)) x) := by
    have hpair := W.pairValue_le (Fin.last W.lastStage) b (Fin.last W.lastStage) hx hx1
    have hterm := W.pairValue_terminal b hx hx1
    rw [hbres] at hterm
    have h1 := le_max_left (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))
    have h2 := le_max_right (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))
    linarith
  -- The entry segment stays above the midpoint value at stage zero.
  have hentry (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
      α * W.benchmark 0 ≤ W.mixtureValue 0 (mix (vertex 0) p x) := by
    have hmixeq : mix (vertex 0) p x = mix (vertex 0) (vertex c) (x * (1 / 2)) := by
      funext i
      simp only [p, mix]
      ring
    rw [hmixeq]
    have hpair := W.pairValue_le 0 0 c (s := x * (1 / 2)) (by nlinarith) (by nlinarith)
    have hopt : W.residual c 0 ≤ W.residual 0 0 := by
      have h := W.residual_le_gain c 0
      rwa [← W.residual_self 0] at h
    have hmono := W.pairValue_half_le 0 0 c (x * (1 / 2)) (by nlinarith)
    have hb := hprefix 0 (Fin.zero_le c)
    have hP0 := W.benchmark_nonneg 0
    nlinarith [mul_le_mul_of_nonneg_right hαβ hP0]
  exact ⟨{
    anchor := p
    entry := PolygonalPath.segment (vertex 0) p
    exit := PolygonalPath.twoSegments p (vertex b) (vertex (Fin.last W.lastStage))
    anchor_mem := hp
    entry_mem := PolygonalPath.along_segment (fun x hx hx1 =>
      (simplex_vertex 0).mix hp hx hx1)
    exit_mem := PolygonalPath.along_twoSegments
      (fun x hx hx1 => hp.mix (simplex_vertex b) hx hx1)
      (fun x hx hx1 => (simplex_vertex b).mix (simplex_vertex _) hx hx1)
    entry_start := rfl
    entry_finish := PolygonalPath.segment_terminal _ _
    exit_start := rfl
    exit_finish := rfl
    persistence := hpersist
    safe_entry := PolygonalPath.along_segment hentry
    safe_exit := PolygonalPath.along_twoSegments hexit1 hexit2
    segments := le_rfl }, rfl, rfl, rfl⟩

end
