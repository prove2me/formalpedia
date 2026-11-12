-- Prove2me | solution 1 for EntropyLocalCoord.Leader.ineff_chain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:34.21623+00:00
-- url     : https://prove2.me/submissions/ad2197cc-a3bd-4e92-b738-ff9c06d69f53

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model
import Definitions.Def_EntropyLocalCoord_Leader_Information

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace EntropyLocalCoord.Dev.Cut

open EntropyLocalCoord.Leader

/-- Uniform measure on `Bool`. -/
noncomputable def μB : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure μB := by unfold μB; infer_instance

lemma μB_real (b : Bool) : μB.real {b} = 1 / 2 := by
  simp [μB, Measure.real, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b),
    PMF.uniformOfFintype_apply]

lemma integral_μB (g : Bool → ℝ) : ∫ b, g b ∂μB = (g true + g false) / 2 := by
  rw [integral_fintype (Integrable.of_finite)]
  simp [μB_real, Fintype.sum_bool]
  ring

/-- The sample space. -/
noncomputable def P (k : ℕ) : Measure (Fin k → Bool) := Measure.pi (fun _ => μB)

instance (k : ℕ) : IsProbabilityMeasure (P k) := by unfold P; infer_instance

lemma integral_coord {k : ℕ} (g : Bool → ℝ) (j : Fin k) :
    ∫ ω, g (ω j) ∂(P k) = (g true + g false) / 2 := by
  have h := (measurePreserving_eval (fun _ : Fin k => μB) j)
  have : ∫ ω, g (ω j) ∂(P k) = ∫ b, g b ∂(Measure.map (fun ω : Fin k → Bool => ω j) (P k)) := by
    rw [integral_map (measurable_pi_apply j).aemeasurable ((measurable_of_finite g).aestronglyMeasurable)]
  rw [this]
  have h2 : Measure.map (fun ω : Fin k → Bool => ω j) (P k) = μB := h.map_eq
  rw [h2, integral_μB]

/-- sign function -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

/-- any profile: the sigma algebra is below the ambient one. -/
lemma sourceSigma_le {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S)
    (i : Fin n) : sourceSigma π.Z (S.B i) ≤ π.mΩ := by
  refine iSup₂_le fun j _ => ?_
  exact (π.Z_measurable j).comap_le

lemma memLp_two {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S) (i : Fin n) :
    MemLp (π.X i) 2 π.P := by
  have hm : Measurable (π.X i) := (π.X_measurable i).mono (sourceSigma_le π i) le_rfl
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  by_contra h
  have := π.second_moment i
  rw [integral_undef h] at this
  exact zero_ne_one this

lemma cov_le_one {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S)
    (i j : Fin n) : π.cov i j ≤ 1 := by
  have hi := memLp_two π i
  have hj := memLp_two π j
  have hii : Integrable (fun ω => π.X i ω ^ 2) π.P := (memLp_two_iff_integrable_sq
    (((π.X_measurable i).mono (sourceSigma_le π i) le_rfl).aestronglyMeasurable)).1 hi
  have hjj : Integrable (fun ω => π.X j ω ^ 2) π.P := (memLp_two_iff_integrable_sq
    (((π.X_measurable j).mono (sourceSigma_le π j) le_rfl).aestronglyMeasurable)).1 hj
  have hij : Integrable (π.X i * π.X j) π.P := hi.integrable_mul hj
  unfold CoordinationProfile.cov
  rw [covariance_eq_sub hi hj, π.mean_zero i]
  simp only [zero_mul, sub_zero]
  have : ∫ ω, (π.X i * π.X j) ω ∂π.P ≤ ∫ ω, (π.X i ω ^ 2 + π.X j ω ^ 2) / 2 ∂π.P := by
    refine integral_mono hij ((hii.add hjj).div_const 2) fun ω => ?_
    simp only [Pi.mul_apply]
    nlinarith [sq_nonneg (π.X i ω - π.X j ω)]
  have h2 : ∫ ω, (π.X i ω ^ 2 + π.X j ω ^ 2) / 2 ∂π.P = 1 := by
    rw [integral_div, integral_add hii hjj, π.second_moment i, π.second_moment j]; norm_num
  have : (∫ ω, π.X i ω * π.X j ω ∂π.P) ≤ 1 := by simpa [h2] using this
  simpa using this

/-- Cost is nonnegative for any profile. -/
theorem cost_nonneg {n k : ℕ} {S : InformationSkeleton n k} (G : SimpleGraph (Fin n))
    (π : CoordinationProfile S) : 0 ≤ cost G π := by
  unfold cost
  refine div_nonneg (Finset.sum_nonneg fun e _ => ?_) (Nat.cast_nonneg _)
  induction e using Sym2.ind with
  | _ i j =>
    simp only [CoordinationProfile.edgeLoss, Sym2.lift_mk]
    linarith [cov_le_one π i j]

/-- Coordinate profile for a leader assignment. -/
noncomputable def cutProfile {n k : ℕ} (S : InformationSkeleton n k) (L : Fin n → Fin k)
    (hL : ∀ i, L i ∈ S.B i) : CoordinationProfile S where
  Ω := Fin k → Bool
  P := P k
  α := fun _ => Bool
  Z := fun j ω => ω j
  Z_measurable := fun j => measurable_pi_apply j
  Z_indep := iIndepFun_pi (μ := fun _ : Fin k => μB) (X := fun _ => (id : Bool → Bool))
    (fun _ => measurable_id.aemeasurable)
  X := fun i ω => sgn (ω (L i))
  X_measurable := by
    intro i
    have h1 : Measurable[MeasurableSpace.comap (fun ω : Fin k → Bool => ω (L i)) inferInstance]
        (fun ω : Fin k → Bool => ω (L i)) := comap_measurable _
    have h2 : MeasurableSpace.comap (fun ω : Fin k → Bool => ω (L i)) inferInstance ≤
        sourceSigma (fun j (ω : Fin k → Bool) => ω j) (S.B i) :=
      le_iSup₂ (f := fun j (_ : j ∈ S.B i) =>
        MeasurableSpace.comap (fun ω : Fin k → Bool => ω j) inferInstance) (L i) (hL i)
    exact (measurable_of_finite sgn).comp (h1.mono h2 le_rfl)
  mean_zero := by
    intro i
    have := integral_coord (k := k) sgn (L i)
    simpa [sgn] using this
  second_moment := by
    intro i
    have := integral_coord (k := k) (fun b => sgn b ^ 2) (L i)
    simpa [sgn_sq] using this

lemma cov_cut {n k : ℕ} (S : InformationSkeleton n k) (L : Fin n → Fin k)
    (hL : ∀ i, L i ∈ S.B i) (i j : Fin n) :
    (cutProfile S L hL).cov i j = if L i = L j then 1 else 0 := by
  have hi := memLp_two (cutProfile S L hL) i
  have hj := memLp_two (cutProfile S L hL) j
  unfold CoordinationProfile.cov
  by_cases h : L i = L j
  · rw [if_pos h, covariance_eq_sub hi hj, (cutProfile S L hL).mean_zero i]
    have : ∫ ω, ((cutProfile S L hL).X i * (cutProfile S L hL).X j) ω ∂(cutProfile S L hL).P = 1 := by
      have := (cutProfile S L hL).second_moment i
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp [cutProfile, h, sq]
      rfl
    simpa using this
  · rw [if_neg h]
    refine IndepFun.covariance_eq_zero ?_ hi hj
    have hind := (cutProfile S L hL).Z_indep
    have := hind.indepFun h
    exact this.comp (φ := sgn) (ψ := sgn) (measurable_of_finite sgn) (measurable_of_finite sgn)

lemma cutProfile_leader {n k : ℕ} (S : InformationSkeleton n k) (L : Fin n → Fin k)
    (hL : ∀ i, L i ∈ S.B i) : (cutProfile S L hL).IsLeader := by
  refine ⟨fun i ω => ?_, fun i j => ?_⟩
  · cases h : ω (L i) <;> simp [cutProfile, sgn, h]
  · rw [cov_cut]; split_ifs <;> simp

lemma cost_cut {n k : ℕ} (G : SimpleGraph (Fin n)) (S : InformationSkeleton n k)
    (L : Fin n → Fin k) (hL : ∀ i, L i ∈ S.B i) :
    cost G (cutProfile S L hL) = cutFraction G L := by
  classical
  unfold cost cutFraction
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [CoordinationProfile.edgeLoss, Sym2.lift_mk, cov_cut]
    have : (∃ i j, s(a, b) = s(i, j) ∧ L i ≠ L j) ↔ L a ≠ L b := by
      constructor
      · rintro ⟨i, j, h, hne⟩
        rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hne
        · exact fun h => hne h.symm
      · exact fun h => ⟨a, b, rfl, h⟩
    rw [if_congr this rfl rfl]
    by_cases h : L a = L b <;> simp [h]

/-- Reusable: a cut profile exists. -/
theorem exists_cut_profile {n k : ℕ} (G : SimpleGraph (Fin n)) (S : InformationSkeleton n k)
    (L : Fin n → Fin k) (hL : ∀ i, L i ∈ S.B i) :
    ∃ π : CoordinationProfile S, π.IsLeader ∧ cost G π = cutFraction G L :=
  ⟨cutProfile S L hL, cutProfile_leader S L hL, cost_cut G S L hL⟩

end EntropyLocalCoord.Dev.Cut

end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open EntropyLocalCoord.Leader EntropyLocalCoord.Dev.Cut in
theorem EntropyLocalCoord.Leader.chk_ineff_chain {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : InformationSkeleton n k) :
    (∃ π : CoordinationProfile S, π.IsLeader ∧ cost G π ≤ 1) ∧
      Ineff G S ≤ Ibin G S ∧ Ibin G S ≤ Ileader G S ∧ Ileader G S ≤ 1 := by
  classical
  let L : Fin n → Fin k := fun i => (S.nonempty i).choose
  have hL : ∀ i, L i ∈ S.B i := fun i => (S.nonempty i).choose_spec
  obtain ⟨π, hπ, hc⟩ := exists_cut_profile G S L hL
  have hcut : cutFraction G L ≤ 1 := by
    unfold cutFraction
    rcases Nat.eq_zero_or_pos G.edgeFinset.card with h0 | hpos
    · simp [h0]
    · rw [div_le_one (by exact_mod_cast hpos)]
      exact_mod_cast Finset.card_filter_le _ _
  have hle : cost G π ≤ 1 := hc ▸ hcut
  have bdd : ∀ s : Set ℝ, (∀ c ∈ s, ∃ π' : CoordinationProfile S, cost G π' = c) → BddBelow s :=
    fun s hs => ⟨0, fun c hc => by obtain ⟨π', rfl⟩ := hs c hc; exact cost_nonneg G π'⟩
  have h2 : Ibin G S ≤ Ileader G S := by
    refine le_csInf ⟨_, π, hπ, rfl⟩ ?_
    rintro c ⟨π', hπ', rfl⟩
    exact csInf_le (bdd _ (by rintro c ⟨π'', _, h⟩; exact ⟨π'', h⟩)) ⟨π', hπ'.1, rfl⟩
  have h1 : Ineff G S ≤ Ibin G S := by
    refine le_csInf ⟨_, π, hπ.1, rfl⟩ ?_
    rintro c ⟨π', hπ', rfl⟩
    exact csInf_le (bdd _ (by rintro c ⟨π'', h⟩; exact ⟨π'', h⟩)) ⟨π', rfl⟩
  have h3 : Ileader G S ≤ 1 := by
    have : Ileader G S ≤ cost G π :=
      csInf_le (bdd _ (by rintro c ⟨π'', _, h⟩; exact ⟨π'', h⟩)) ⟨π, hπ, rfl⟩
    exact this.trans hle
  exact ⟨⟨π, hπ, hle⟩, h1, h2, h3⟩
end

theorem solution : type_of% @EntropyLocalCoord.Leader.chk_ineff_chain := @EntropyLocalCoord.Leader.chk_ineff_chain
