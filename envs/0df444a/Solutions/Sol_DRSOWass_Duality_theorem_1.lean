-- Prove2me | solution 1 for DRSOWass.Duality.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:30:18.966671+00:00
-- url     : https://prove2.me/submissions/5d8ecb62-bc9d-4844-9b0b-eb2e6014041a

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting
import Theorems.Thm_DRSOWass_Duality_proposition_1

open MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

namespace DRSOWWeakAux

open DRSOWass.Duality ModelRiskOT.Duality

lemma ereal_alg (a1 a2 b1 b2 c : ENNReal) (hb1 : b1 ≠ ⊤) (hc : c ≠ ⊤)
    (h : a1 + b1 ≤ c + a2 + b2) :
    (a1 : EReal) - a2 ≤ (c : EReal) - ((b1 : EReal) - b2) := by
  by_cases ha2 : a2 = ⊤
  · subst ha2; simp
  by_cases hb2 : b2 = ⊤
  · subst hb2
    rw [EReal.coe_ennreal_top, EReal.sub_top, EReal.sub_bot (by simp)]; exact le_top
  have ha1 : a1 ≠ ⊤ := by
    intro h1; subst h1; simp_all [ENNReal.add_eq_top]
  lift a1 to NNReal using ha1
  lift a2 to NNReal using ha2
  lift b1 to NNReal using hb1
  lift b2 to NNReal using hb2
  lift c to NNReal using hc
  simp only [EReal.coe_nnreal_eq_coe_real]
  have h' : (a1:ℝ) + b1 ≤ c + a2 + b2 := by exact_mod_cast h
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

lemma pw_alg (u : ℝ) (v : EReal) (L : ℝ) (hL : 0 ≤ L) (h : v ≤ ((L - u : ℝ) : EReal)) :
    ENNReal.ofReal u + v.toENNReal ≤ ENNReal.ofReal L + ENNReal.ofReal (-u) + (-v).toENNReal := by
  induction v using EReal.rec with
  | bot => simp
  | top => exact absurd h (EReal.coe_lt_top _).not_ge
  | coe v =>
    have h' : v ≤ L - u := by exact_mod_cast h
    simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
    rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
    · rw [← ENNReal.ofReal_add hu hv, add_assoc]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [ENNReal.ofReal_of_nonpos hv, add_zero, add_right_comm,
        ← ENNReal.ofReal_add hL (by linarith)]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [ENNReal.ofReal_of_nonpos hu, zero_add, ← ENNReal.ofReal_add hL (by linarith)]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [ENNReal.ofReal_of_nonpos hu, ENNReal.ofReal_of_nonpos hv, zero_add]; exact bot_le

variable {Ξ : Type*} [MetricSpace Ξ] [SecondCountableTopology Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]

lemma phi_le_of (Ψ : Ξ → ℝ) (p lam : ℝ) (ξ ζ : Ξ) :
    Phi Ψ p lam ζ ≤ ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal) :=
  iInf_le (fun ξ => ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal)) ξ

lemma phi_le_neg (Ψ : Ξ → ℝ) (p lam : ℝ) (hp : 0 < p) (ζ : Ξ) :
    Phi Ψ p lam ζ ≤ ((-Ψ ζ : ℝ) : EReal) := by
  have := phi_le_of Ψ p lam ζ ζ
  simpa [Real.zero_rpow hp.ne'] using this

lemma cont_term (Ψ : Ξ → ℝ) (p lam : ℝ) (hp : 0 < p) (ξ : Ξ) :
    Continuous fun ζ => lam * dist ξ ζ ^ p - Ψ ξ := by
  have : Continuous fun ζ => dist ξ ζ := continuous_const.dist continuous_id
  exact (continuous_const.mul (this.rpow_const (fun _ => Or.inr hp.le))).sub continuous_const

lemma phi_measurable (Ψ : Ξ → ℝ) (p lam : ℝ) (hp : 0 < p) : Measurable (Phi Ψ p lam) := by
  apply UpperSemicontinuous.measurable
  show UpperSemicontinuous fun ζ => ⨅ ξ : Ξ, ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal)
  exact upperSemicontinuous_iInf fun ξ =>
    (continuous_coe_real_ereal.comp (cont_term Ψ p lam hp ξ)).upperSemicontinuous

lemma extIntegral_real {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    extIntegral μ (fun x => (f x : EReal)) =
      ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
        ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal) := by
  rfl

lemma phi_pos_ne_top (ν : Measure Ξ) (Ψ : Ξ → ℝ) (hΨ : Integrable Ψ ν) (p lam : ℝ) (hp : 0 < p) :
    ∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top hΨ.neg.lintegral_lt_top.ne (lintegral_mono fun ζ => ?_)
  exact EReal.toENNReal_le_toENNReal (phi_le_neg Ψ p lam hp ζ)

lemma extIntegral_phi_ne_top (ν : Measure Ξ) (Ψ : Ξ → ℝ) (hΨ : Integrable Ψ ν) (p lam : ℝ)
    (hp : 0 < p) : extIntegral ν (Phi Ψ p lam) ≠ ⊤ := by
  unfold extIntegral
  intro h
  have h1 := phi_pos_ne_top ν Ψ hΨ p lam hp
  have : ((∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν : ENNReal) : EReal) -
      ((∫⁻ ζ, (-Phi Ψ p lam ζ).toENNReal ∂ν : ENNReal) : EReal) ≤
      ((∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν : ENNReal) : EReal) - 0 :=
    EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)
  rw [h, sub_zero, top_le_iff, EReal.coe_ennreal_eq_top_iff] at this
  exact h1 this

lemma coupling_bound (ν : Measure Ξ) (Ψ : Ξ → ℝ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 ≤ lam)
    (μ : Measure Ξ) (γ : Measure (Ξ × Ξ)) (h1 : γ.map Prod.fst = μ) (h2 : γ.map Prod.snd = ν)
    (hC : ∫⁻ w, ENNReal.ofReal (dist w.1 w.2 ^ p) ∂γ ≠ ⊤) :
    extIntegral μ (fun ξ => (Ψ ξ : EReal)) ≤
      ((lam * (∫⁻ w, ENNReal.ofReal (dist w.1 w.2 ^ p) ∂γ).toReal : ℝ) : EReal) -
        extIntegral ν (Phi Ψ p lam) := by
  set C := ∫⁻ w, ENNReal.ofReal (dist w.1 w.2 ^ p) ∂γ with hCdef
  have hΦm := phi_measurable Ψ p lam hp
  have key : ∀ w : Ξ × Ξ, ENNReal.ofReal (Ψ w.1) + (Phi Ψ p lam w.2).toENNReal ≤
      ENNReal.ofReal lam * ENNReal.ofReal (dist w.1 w.2 ^ p) + ENNReal.ofReal (-Ψ w.1) +
        (-Phi Ψ p lam w.2).toENNReal := by
    intro w
    rw [← ENNReal.ofReal_mul hlam]
    exact pw_alg _ _ _ (mul_nonneg hlam (by positivity)) (phi_le_of Ψ p lam w.1 w.2)
  have hint := lintegral_mono (μ := γ) key
  have mΨp : Measurable fun ξ => ENNReal.ofReal (Ψ ξ) := ENNReal.measurable_ofReal.comp hΨm
  have mΨn : Measurable fun ξ => ENNReal.ofReal (-Ψ ξ) := ENNReal.measurable_ofReal.comp hΨm.neg
  have mΦp : Measurable fun ζ => (Phi Ψ p lam ζ).toENNReal := measurable_ereal_toENNReal.comp hΦm
  have mΦn : Measurable fun ζ => (-Phi Ψ p lam ζ).toENNReal :=
    measurable_ereal_toENNReal.comp hΦm.neg
  have e1 : ∫⁻ w, ENNReal.ofReal (Ψ w.1) ∂γ = ∫⁻ ξ, ENNReal.ofReal (Ψ ξ) ∂μ := by
    rw [← h1, lintegral_map mΨp measurable_fst]
  have e2 : ∫⁻ w, ENNReal.ofReal (-Ψ w.1) ∂γ = ∫⁻ ξ, ENNReal.ofReal (-Ψ ξ) ∂μ := by
    rw [← h1, lintegral_map mΨn measurable_fst]
  have e3 : ∫⁻ w, (Phi Ψ p lam w.2).toENNReal ∂γ = ∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν := by
    rw [← h2, lintegral_map mΦp measurable_snd]
  have e4 : ∫⁻ w, (-Phi Ψ p lam w.2).toENNReal ∂γ = ∫⁻ ζ, (-Phi Ψ p lam ζ).toENNReal ∂ν := by
    rw [← h2, lintegral_map mΦn measurable_snd]
  have mΨp' : Measurable fun w : Ξ × Ξ => ENNReal.ofReal (Ψ w.1) := mΨp.comp measurable_fst
  rw [lintegral_add_left mΨp', lintegral_add_left' ?_,
    lintegral_add_left' ?_, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, e1, e2, e3, e4]
    at hint
  rotate_left
  · exact (measurable_const.mul ((ENNReal.measurable_ofReal.comp
      ((measurable_fst.dist measurable_snd).pow_const p)))).aemeasurable
  · exact ((measurable_const.mul ((ENNReal.measurable_ofReal.comp
      ((measurable_fst.dist measurable_snd).pow_const p)))).add
      (mΨn.comp measurable_fst)).aemeasurable
  have := ereal_alg _ _ _ _ _ (phi_pos_ne_top ν Ψ hΨ p lam hp)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) hint
  rw [extIntegral_real]
  unfold extIntegral
  convert this using 2
  rw [← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul hlam, EReal.coe_ennreal_ofReal,
    max_eq_left (mul_nonneg hlam ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hC]

lemma extIntegral_of_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) :
    extIntegral μ (fun x => (f x : EReal)) = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  rw [extIntegral_real, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, EReal.coe_sub,
    EReal.coe_ennreal_toReal hf.lintegral_lt_top.ne,
    EReal.coe_ennreal_toReal
      (by simpa using hf.neg.lintegral_lt_top.ne : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤)]

lemma mix_feasible (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (hΨm : Measurable Ψ)
    (p θ : ℝ) (hp : 0 < p)
    (T1 T2 : Ξ → Ξ) (h1 : Measurable T1) (h2 : Measurable T2)
    (hi1 : Integrable (fun ζ => Ψ (T1 ζ)) ν) (hi2 : Integrable (fun ζ => Ψ (T2 ζ)) ν)
    (hc1 : Integrable (fun ζ => dist (T1 ζ) ζ ^ p) ν)
    (hc2 : Integrable (fun ζ => dist (T2 ζ) ζ ^ p) ν)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcost : a * ∫ ζ, dist (T1 ζ) ζ ^ p ∂ν + (1 - a) * ∫ ζ, dist (T2 ζ) ζ ^ p ∂ν ≤ θ ^ p) :
    ((a * ∫ ζ, Ψ (T1 ζ) ∂ν + (1 - a) * ∫ ζ, Ψ (T2 ζ) ∂ν : ℝ) : EReal) ≤ vP Ψ ν p θ := by
  set F1 : Ξ → Ξ × Ξ := fun ζ => (T1 ζ, ζ) with hF1
  set F2 : Ξ → Ξ × Ξ := fun ζ => (T2 ζ, ζ) with hF2
  have mF1 : Measurable F1 := h1.prodMk measurable_id
  have mF2 : Measurable F2 := h2.prodMk measurable_id
  set γ : Measure (Ξ × Ξ) := ENNReal.ofReal a • ν.map F1 + ENNReal.ofReal (1 - a) • ν.map F2
    with hγ
  have hsum : ENNReal.ofReal a + ENNReal.ofReal (1 - a) = 1 := by
    rw [← ENNReal.ofReal_add ha0 (by linarith)]; simp
  have hγp : IsProbabilityMeasure γ := by
    constructor
    simp only [hγ, Measure.add_apply, Measure.smul_apply, Measure.map_apply mF1 MeasurableSet.univ,
      Measure.map_apply mF2 MeasurableSet.univ, Set.preimage_univ, measure_univ, smul_eq_mul,
      mul_one, hsum]
  have hsnd : γ.map Prod.snd = ν := by
    rw [hγ, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      Measure.map_map measurable_snd mF1, Measure.map_map measurable_snd mF2]
    have e1 : (Prod.snd ∘ F1) = id := rfl
    have e2 : (Prod.snd ∘ F2) = id := rfl
    rw [e1, e2, Measure.map_id, ← add_smul, hsum, one_smul]
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure Ξ, μ = γ.map Prod.fst := ⟨_, rfl⟩
  have hfst : μ = ENNReal.ofReal a • ν.map T1 + ENNReal.ofReal (1 - a) • ν.map T2 := by
    rw [hμ, hγ, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
      Measure.map_map measurable_fst mF1, Measure.map_map measurable_fst mF2]
    rfl
  have hμp : IsProbabilityMeasure μ := hμ ▸ Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hcm : Measurable fun w : Ξ × Ξ => ENNReal.ofReal (dist w.1 w.2 ^ p) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.dist measurable_snd).pow_const p)
  have hW : wassPow p μ ν ≤ ENNReal.ofReal (θ ^ p) := by
    unfold wassPow RWPI.SqrtLasso.transportCost
    refine (iInf₂_le γ ⟨hγp, hμ.symm, hsnd⟩).trans ?_
    rw [hγ, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_map hcm mF1, lintegral_map hcm mF2]
    simp only [hF1, hF2]
    rw [← ofReal_integral_eq_lintegral_ofReal hc1 (ae_of_all _ fun _ => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal hc2 (ae_of_all _ fun _ => by positivity),
      smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (mul_nonneg ha0 (integral_nonneg fun _ => by positivity))
        (mul_nonneg (by linarith) (integral_nonneg fun _ => by positivity))]
    exact ENNReal.ofReal_le_ofReal hcost
  have hm1 : Integrable Ψ (ν.map T1) :=
    (integrable_map_measure hΨm.aestronglyMeasurable h1.aemeasurable).mpr hi1
  have hm2 : Integrable Ψ (ν.map T2) :=
    (integrable_map_measure hΨm.aestronglyMeasurable h2.aemeasurable).mpr hi2
  have hint : Integrable Ψ μ := by
    rw [hfst]
    exact (hm1.smul_measure ENNReal.ofReal_ne_top).add_measure
      (hm2.smul_measure ENNReal.ofReal_ne_top)
  refine le_trans ?_ (le_iSup₂_of_le (f := fun (μ : Measure Ξ)
    (_ : IsProbabilityMeasure μ ∧ wassPow p μ ν ≤ ENNReal.ofReal (θ ^ p)) =>
      extIntegral μ (fun ξ => (Ψ ξ : EReal))) μ ⟨hμp, hW⟩ le_rfl)
  rw [extIntegral_of_integrable μ Ψ hint, hfst,
    integral_add_measure (hm1.smul_measure ENNReal.ofReal_ne_top)
      (hm2.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map h1.aemeasurable hΨm.aestronglyMeasurable,
    integral_map h2.aemeasurable hΨm.aestronglyMeasurable,
    ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal (by linarith)]
  simp only [smul_eq_mul, le_refl]

lemma select (Ψ : Ξ → ℝ) (p lam : ℝ) (hp : 0 < p) (φ : Ξ → ℝ) (hφ : Measurable φ)
    (hlt : ∀ ζ, Phi Ψ p lam ζ < (φ ζ : EReal)) (ξ0 : Ξ) :
    ∃ T : Ξ → Ξ, Measurable T ∧ ∀ ζ, lam * dist (T ζ) ζ ^ p - Ψ (T ζ) < φ ζ := by
  classical
  set O : Ξ → ℚ → Set Ξ := fun ξ q => {ζ | lam * dist ξ ζ ^ p - Ψ ξ < q} with hOdef
  have hO : ∀ ξ q, IsOpen (O ξ q) := fun ξ q =>
    isOpen_lt (cont_term Ψ p lam hp ξ) continuous_const
  have hcount : ∀ q : ℚ, ∃ e : ℕ → Ξ, ∀ ζ, (∃ ξ, ζ ∈ O ξ q) → ∃ n, ζ ∈ O (e n) q := by
    intro q
    obtain ⟨S, hSc, hS⟩ :=
      TopologicalSpace.isOpen_iUnion_countable (fun ξ => O ξ q) (fun ξ => hO ξ q)
    obtain ⟨e, he⟩ := (hSc.union (Set.countable_singleton ξ0)).exists_eq_range
      ⟨ξ0, Or.inr rfl⟩
    refine ⟨e, fun ζ ⟨ξ, hξ⟩ => ?_⟩
    have h1 : ζ ∈ ⋃ ξ ∈ S, O ξ q := hS ▸ Set.mem_iUnion.mpr ⟨ξ, hξ⟩
    obtain ⟨ξ', hξ'S, hζ⟩ := Set.mem_iUnion₂.mp h1
    have h2 : ξ' ∈ Set.range e := he ▸ Or.inl hξ'S
    obtain ⟨n, rfl⟩ := h2
    exact ⟨n, hζ⟩
  choose e he using hcount
  obtain ⟨g, hgs⟩ := exists_surjective_nat (ℚ × ℕ)
  let C : Ξ → ℕ → Prop := fun ζ k =>
    (((g k).1 : ℝ) < φ ζ) ∧ ζ ∈ O (e (g k).1 (g k).2) (g k).1
  have hex : ∀ ζ, ∃ k, C ζ k := by
    intro ζ
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.mp (hlt ζ)
    have h3 : ∃ ξ, ζ ∈ O ξ q := by
      obtain ⟨ξ, hξ⟩ := iInf_lt_iff.mp hq1
      exact ⟨ξ, by simp only [O, Set.mem_ofPred_eq]; exact_mod_cast hξ⟩
    obtain ⟨n, hn⟩ := he q ζ h3
    obtain ⟨k, hg⟩ := hgs (q, n)
    refine ⟨k, ?_⟩
    show (((g k).1 : ℝ) < φ ζ) ∧ ζ ∈ O (e (g k).1 (g k).2) (g k).1
    rw [hg]
    exact ⟨by exact_mod_cast hq2, hn⟩
  have hidx : Measurable fun ζ => Nat.find (hex ζ) := by
    refine measurable_find hex (fun k => ?_)
    exact (measurableSet_lt measurable_const hφ).inter (hO _ _).measurableSet
  refine ⟨fun ζ => e (g (Nat.find (hex ζ))).1 (g (Nat.find (hex ζ))).2, ?_, ?_⟩
  · exact (measurable_from_nat (f := fun k => e (g k).1 (g k).2)).comp hidx
  · intro ζ
    have hs := Nat.find_spec (hex ζ)
    exact lt_trans hs.2 hs.1

lemma lagrange (P : ℝ → ℝ → Prop) (t s v0 : ℝ) (ht : 0 < t) (h0 : P 0 v0)
    (hmix : ∀ c1 v1 c2 v2 a, P c1 v1 → P c2 v2 → 0 ≤ a → a ≤ 1 → a * c1 + (1 - a) * c2 ≤ t →
      a * v1 + (1 - a) * v2 ≤ s) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ c v, P c v → v - lam * c ≤ s - lam * t := by
  have hone : ∀ c v, P c v → c ≤ t → v ≤ s := fun c v h hc => by
    have := hmix c v c v 1 h h zero_le_one le_rfl (by simpa using hc); simpa using this
  have hslope : ∀ c1 v1 c2 v2, P c1 v1 → P c2 v2 → c1 < t → t < c2 →
      (v2 - s) / (c2 - t) ≤ (s - v1) / (t - c1) := by
    intro c1 v1 c2 v2 h1 h2 hc1 hc2
    have hd : 0 < c2 - c1 := by linarith
    set a := (c2 - t) / (c2 - c1) with ha
    have ha0 : 0 ≤ a := div_nonneg (by linarith) hd.le
    have ha1 : a ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hac : a * c1 + (1 - a) * c2 = t := by rw [ha]; field_simp; ring
    have hm := hmix c1 v1 c2 v2 a h1 h2 ha0 ha1 hac.le
    have hm2 := mul_le_mul_of_nonneg_left hm hd.le
    have e2 : (c2 - c1) * (a * v1 + (1 - a) * v2) = (c2 - t) * v1 + (t - c1) * v2 := by
      rw [ha]; field_simp; ring
    rw [e2] at hm2
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  set A : Set ℝ := insert 0 {r | ∃ c v, P c v ∧ t < c ∧ r = (v - s) / (c - t)} with hA
  have hv0 : v0 ≤ s := hone 0 v0 h0 ht.le
  have hbdd : BddAbove A := by
    refine ⟨(s - v0) / t, ?_⟩
    rintro r (rfl | ⟨c, v, hP, hc, rfl⟩)
    · exact div_nonneg (by linarith) ht.le
    · have := hslope 0 v0 c v h0 hP ht hc
      simpa using this
  refine ⟨sSup A, le_csSup hbdd (Set.mem_insert _ _), fun c v hP => ?_⟩
  rcases lt_trichotomy c t with hc | hc | hc
  · have hle : sSup A ≤ (s - v) / (t - c) := by
      refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
      rintro r (rfl | ⟨c2, v2, hP2, hc2, rfl⟩)
      · exact div_nonneg (by linarith [hone c v hP hc.le]) (by linarith)
      · exact hslope c v c2 v2 hP hP2 hc hc2
    rw [le_div_iff₀ (by linarith)] at hle
    nlinarith
  · subst hc; linarith [hone c v hP le_rfl]
  · have hmem : (v - s) / (c - t) ∈ A := Or.inr ⟨c, v, hP, hc, rfl⟩
    have hle := le_csSup hbdd hmem
    rw [div_le_iff₀ (by linarith)] at hle
    nlinarith

lemma g_cont : Continuous fun q : EReal × ℝ => (((-q.2 : ℝ) : EReal) - q.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨v, u⟩
  have h1 : ContinuousAt (fun q : EReal × ℝ => ((((-q.2 : ℝ) : EReal)), -q.1)) (v, u) :=
    ((continuous_coe_real_ereal.comp (continuous_snd.neg)).prodMk
      (continuous_neg.comp continuous_fst)).continuousAt
  have h2 : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) ((((-u : ℝ) : EReal)), -v) :=
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  exact h2.comp_of_eq h1 rfl

lemma D_meas {X : Type*} [MeasurableSpace X] (Φ : X → EReal) (Ψ : X → ℝ) (h1 : Measurable Φ)
    (h2 : Measurable Ψ) : Measurable fun ζ => ((((-Ψ ζ : ℝ) : EReal) - Φ ζ)).toENNReal :=
  measurable_ereal_toENNReal.comp (g_cont.measurable.comp (h1.prodMk h2))

lemma pw_ident (u : ℝ) (v : EReal) (hv : v ≤ ((-u : ℝ) : EReal)) :
    v.toENNReal + ENNReal.ofReal u + (((-u : ℝ) : EReal) - v).toENNReal =
      ENNReal.ofReal (-u) + (-v).toENNReal := by
  induction v using EReal.rec with
  | bot => simp [EReal.sub_bot]
  | top => exact absurd hv (not_le.mpr (EReal.coe_lt_top _))
  | coe v =>
    have h' : v ≤ -u := by exact_mod_cast hv
    rw [← EReal.coe_sub, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness)
      (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_ofReal']
    rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hw | hw <;>
      simp only [max_eq_left, max_eq_right, hu, hw, neg_nonneg, neg_nonpos] <;>
      (rw [max_eq_left (by linarith)]; linarith)

lemma trunc_bound (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (hΨm : Measurable Ψ)
    (hΨ : Integrable Ψ ν) (p : ℝ) (hp : 0 < p) (lam : ℝ) (r : ℝ)
    (H : ∀ T : Ξ → Ξ, Measurable T → Integrable (fun ζ => Ψ (T ζ)) ν →
      Integrable (fun ζ => dist (T ζ) ζ ^ p) ν → r ≤ ∫ ζ, (lam * dist (T ζ) ζ ^ p - Ψ (T ζ)) ∂ν)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ ζ, min ((((-Ψ ζ : ℝ) : EReal) - Phi Ψ p lam ζ).toENNReal) (N : ENNReal) ∂ν ≤
      ENNReal.ofReal (-(∫ ζ, Ψ ζ ∂ν) - r + ε) := by
  have hΦm := phi_measurable Ψ p lam hp
  set D : Ξ → ENNReal := fun ζ => (((-Ψ ζ : ℝ) : EReal) - Phi Ψ p lam ζ).toENNReal with hD
  have hDm : Measurable D := D_meas _ _ hΦm hΨm
  set m : Ξ → ℝ := fun ζ => (min (D ζ) (N : ENNReal)).toReal with hm
  have hmm : Measurable m := (hDm.min measurable_const).ennreal_toReal
  have hmN : ∀ ζ, m ζ ≤ N := fun ζ => by
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top N) (min_le_right (D ζ) (N : ENNReal))
    simpa using this
  have hm0 : ∀ ζ, 0 ≤ m ζ := fun ζ => ENNReal.toReal_nonneg
  have hmint : Integrable m ν := Integrable.of_bound hmm.aestronglyMeasurable N
    (ae_of_all _ fun ζ => by rw [Real.norm_eq_abs, abs_of_nonneg (hm0 ζ)]; exact hmN ζ)
  set φ : Ξ → ℝ := fun ζ => -Ψ ζ - m ζ + ε / 2 with hφ
  have hφm : Measurable φ := (hΨm.neg.sub hmm).add measurable_const
  have hlt : ∀ ζ, Phi Ψ p lam ζ < (φ ζ : EReal) := by
    intro ζ
    have hle := phi_le_neg Ψ p lam hp ζ
    show Phi Ψ p lam ζ < ((-Ψ ζ - (min ((((-Ψ ζ : ℝ) : EReal) - Phi Ψ p lam ζ).toENNReal)
      (N : ENNReal)).toReal + ε / 2 : ℝ) : EReal)
    generalize Phi Ψ p lam ζ = v at hle ⊢
    induction v using EReal.rec with
    | bot => exact EReal.bot_lt_coe _
    | top => exact absurd hle (not_le.mpr (EReal.coe_lt_top _))
    | coe v =>
      have h' : v ≤ -Ψ ζ := by exact_mod_cast hle
      rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (min_le_left (ENNReal.ofReal (-Ψ ζ - v)) (N : ENNReal))
      rw [ENNReal.toReal_ofReal (by linarith)] at h2
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have ξ0 : Ξ := (nonempty_of_isProbabilityMeasure ν).some
  obtain ⟨T, hTm, hT⟩ := select Ψ p lam hp φ hφm hlt ξ0
  set A : ℕ → Set Ξ := fun M => {ζ | dist (T ζ) ζ ^ p ≤ M ∧ |Ψ (T ζ)| ≤ M} with hA
  have hAm : ∀ M, MeasurableSet (A M) := fun M =>
    (measurableSet_le ((hTm.dist measurable_id).pow_const p) measurable_const).inter
      (measurableSet_le (hΨm.comp hTm).abs measurable_const)
  have hmono : Antitone fun M => (A M)ᶜ := fun M1 M2 h =>
    Set.compl_subset_compl.mpr (fun ζ ⟨h1, h2⟩ =>
      ⟨h1.trans (by exact_mod_cast h), h2.trans (by exact_mod_cast h)⟩)
  have hinter : ⋂ M, (A M)ᶜ = ∅ := by
    ext ζ
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_forall, not_not]
    obtain ⟨M, hM⟩ := exists_nat_ge (max (dist (T ζ) ζ ^ p) |Ψ (T ζ)|)
    exact ⟨M, le_trans (le_max_left _ _) hM, le_trans (le_max_right _ _) hM⟩
  have htend := tendsto_measure_iInter_atTop (μ := ν)
    (fun M => (hAm M).compl.nullMeasurableSet) hmono ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at htend
  have hpos : (0 : ENNReal) < ENNReal.ofReal (ε / (2 * (N + 1))) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨M, hM⟩ := (htend.eventually (gt_mem_nhds hpos)).exists
  have hMr : ν.real (A M)ᶜ * N ≤ ε / 2 := by
    have h1 : ν.real (A M)ᶜ < ε / (2 * (N + 1)) := ENNReal.toReal_lt_of_lt_ofReal hM
    have h0 : 0 ≤ ν.real (A M)ᶜ := measureReal_nonneg
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ν.real (A M)ᶜ * N ≤ (ε / (2 * (N + 1))) * N :=
          mul_le_mul_of_nonneg_right h1.le hN
      _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  set T' : Ξ → Ξ := (A M).piecewise T id with hT'
  have hT'm : Measurable T' := hTm.piecewise (hAm M) measurable_id
  have hT'A : ∀ ζ ∈ A M, T' ζ = T ζ := fun ζ h => Set.piecewise_eq_of_mem _ _ _ h
  have hT'Ac : ∀ ζ ∉ A M, T' ζ = ζ := fun ζ h => Set.piecewise_eq_of_notMem _ _ _ h
  have hi1 : Integrable (fun ζ => Ψ (T' ζ)) ν := by
    refine Integrable.mono' ((integrable_const (M : ℝ)).add hΨ.abs)
      (hΨm.comp hT'm).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : ζ ∈ A M
    · rw [hT'A ζ h]; have := h.2; simp only [Pi.add_apply]; linarith [abs_nonneg (Ψ ζ)]
    · rw [hT'Ac ζ h]; simp only [Pi.add_apply]; linarith [Nat.cast_nonneg (α := ℝ) M]
  have hdp : ∀ ζ, 0 ≤ dist (T' ζ) ζ ^ p := fun ζ => by positivity
  have hcm' : Measurable fun ζ => dist (T' ζ) ζ ^ p := (hT'm.dist measurable_id).pow_const p
  have hi2 : Integrable (fun ζ => dist (T' ζ) ζ ^ p) ν := by
    refine Integrable.of_bound hcm'.aestronglyMeasurable M (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hdp ζ)]
    by_cases h : ζ ∈ A M
    · rw [hT'A ζ h]; exact h.1
    · rw [hT'Ac ζ h, dist_self, Real.zero_rpow hp.ne']; positivity
  have hH := H T' hT'm hi1 hi2
  have hpt : ∀ ζ, lam * dist (T' ζ) ζ ^ p - Ψ (T' ζ) ≤
      φ ζ + (A M)ᶜ.indicator (fun _ => (N : ℝ)) ζ := by
    intro ζ
    by_cases h : ζ ∈ A M
    · rw [hT'A ζ h, Set.indicator_of_notMem (by simpa using h)]; linarith [hT ζ]
    · rw [hT'Ac ζ h, Set.indicator_of_mem (by simpa using h), dist_self,
        Real.zero_rpow hp.ne', mul_zero, zero_sub]
      simp only [hφ]; linarith [hmN ζ]
  have hφint : Integrable φ ν := (hΨ.neg.sub hmint).add (integrable_const _)
  have hind : Integrable ((A M)ᶜ.indicator (fun _ => (N : ℝ))) ν :=
    (integrable_const _).indicator (hAm M).compl
  have hI : ∫ ζ, (lam * dist (T' ζ) ζ ^ p - Ψ (T' ζ)) ∂ν ≤
      ∫ ζ, (φ ζ + (A M)ᶜ.indicator (fun _ => (N : ℝ)) ζ) ∂ν :=
    integral_mono ((hi2.const_mul lam).sub hi1) (hφint.add hind) hpt
  rw [integral_add hφint hind, integral_indicator_const _ (hAm M).compl, smul_eq_mul] at hI
  have hφI : ∫ ζ, φ ζ ∂ν = -(∫ ζ, Ψ ζ ∂ν) - ∫ ζ, m ζ ∂ν + ε / 2 := by
    simp only [hφ]
    have i1 : Integrable (fun ζ => -Ψ ζ - m ζ) ν := hΨ.neg.sub hmint
    have i2 : Integrable (fun ζ => -Ψ ζ) ν := hΨ.neg
    rw [integral_add i1 (integrable_const _), integral_sub i2 hmint,
      integral_neg, integral_const]
    simp
  have hmI : ∫ ζ, m ζ ∂ν ≤ -(∫ ζ, Ψ ζ ∂ν) - r + ε := by linarith
  have hlin : ∫⁻ ζ, min (D ζ) (N : ENNReal) ∂ν = ENNReal.ofReal (∫ ζ, m ζ ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hmint (ae_of_all _ hm0)]
    refine lintegral_congr fun ζ => ?_
    simp only [hm]
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _))]
  rw [hlin]
  exact ENNReal.ofReal_le_ofReal hmI

lemma key_B (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (hΨm : Measurable Ψ)
    (hΨ : Integrable Ψ ν) (p : ℝ) (hp : 0 < p) (lam : ℝ) (r : ℝ)
    (H : ∀ T : Ξ → Ξ, Measurable T → Integrable (fun ζ => Ψ (T ζ)) ν →
      Integrable (fun ζ => dist (T ζ) ζ ^ p) ν → r ≤ ∫ ζ, (lam * dist (T ζ) ζ ^ p - Ψ (T ζ)) ∂ν) :
    ((r : ℝ) : EReal) ≤ extIntegral ν (Phi Ψ p lam) := by
  have hΦm := phi_measurable Ψ p lam hp
  set D : Ξ → ENNReal := fun ζ => (((-Ψ ζ : ℝ) : EReal) - Phi Ψ p lam ζ).toENNReal with hD
  have hDm : Measurable D := D_meas _ _ hΦm hΨm
  have hr : r ≤ -(∫ ζ, Ψ ζ ∂ν) := by
    have h0 : Integrable (fun ζ : Ξ => dist (id ζ) ζ ^ p) ν := by
      simp only [id, dist_self, Real.zero_rpow hp.ne']; exact integrable_const _
    have := H id measurable_id hΨ h0
    simp only [id, dist_self, Real.zero_rpow hp.ne', mul_zero, zero_sub, integral_neg] at this
    exact this
  have hsup : ∀ ζ, ⨆ N : ℕ, min (D ζ) (N : ENNReal) = D ζ := fun ζ => by
    have := (inf_iSup_eq (D ζ) (fun N : ℕ => (N : ENNReal))).symm
    rw [ENNReal.iSup_natCast] at this
    simpa using this
  have hDint : ∫⁻ ζ, D ζ ∂ν ≤ ENNReal.ofReal (-(∫ ζ, Ψ ζ ∂ν) - r) := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have heq : ∫⁻ ζ, D ζ ∂ν = ⨆ N : ℕ, ∫⁻ ζ, min (D ζ) (N : ENNReal) ∂ν := by
      rw [← lintegral_iSup (fun N => hDm.min measurable_const)
        (fun a b h ζ => min_le_min_left _ (by exact_mod_cast h))]
      exact lintegral_congr fun ζ => (hsup ζ).symm
    rw [heq]
    refine iSup_le fun N => (trunc_bound ν Ψ hΨm hΨ p hp lam r H N ε hε).trans ?_
    refine ENNReal.ofReal_add_le.trans ?_
    rw [ENNReal.ofReal_coe_nnreal]
  have hpt : ∀ ζ, (Phi Ψ p lam ζ).toENNReal + ENNReal.ofReal (Ψ ζ) + D ζ =
      ENNReal.ofReal (-Ψ ζ) + (-Phi Ψ p lam ζ).toENNReal := fun ζ =>
    pw_ident (Ψ ζ) (Phi Ψ p lam ζ) (phi_le_neg Ψ p lam hp ζ)
  have mΦp : Measurable fun ζ => (Phi Ψ p lam ζ).toENNReal := measurable_ereal_toENNReal.comp hΦm
  have mΨp : Measurable fun ξ => ENNReal.ofReal (Ψ ξ) := ENNReal.measurable_ofReal.comp hΨm
  have mΨn : Measurable fun ξ => ENNReal.ofReal (-Ψ ξ) := ENNReal.measurable_ofReal.comp hΨm.neg
  have hI : ∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν + ∫⁻ ζ, ENNReal.ofReal (Ψ ζ) ∂ν + ∫⁻ ζ, D ζ ∂ν =
      ∫⁻ ζ, ENNReal.ofReal (-Ψ ζ) ∂ν + ∫⁻ ζ, (-Phi Ψ p lam ζ).toENNReal ∂ν := by
    have mΦΨ : Measurable fun ζ => (Phi Ψ p lam ζ).toENNReal + ENNReal.ofReal (Ψ ζ) :=
      mΦp.add mΨp
    rw [← lintegral_add_left mΦp, ← lintegral_add_left mΦΨ, ← lintegral_add_left mΨn]
    exact lintegral_congr hpt
  set B1 := ∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν with hB1
  set B2 := ∫⁻ ζ, (-Phi Ψ p lam ζ).toENNReal ∂ν with hB2
  set P := ∫⁻ ζ, ENNReal.ofReal (Ψ ζ) ∂ν with hP
  set Q := ∫⁻ ζ, ENNReal.ofReal (-Ψ ζ) ∂ν with hQ
  set Dd := ∫⁻ ζ, D ζ ∂ν with hDd
  have hB1t : B1 ≠ ⊤ := phi_pos_ne_top ν Ψ hΨ p lam hp
  have hPt : P ≠ ⊤ := hΨ.lintegral_lt_top.ne
  have hQt : Q ≠ ⊤ := by simpa using hΨ.neg.lintegral_lt_top.ne
  have hDt : Dd ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDint
  have hB2t : B2 ≠ ⊤ := by
    intro h; rw [h, add_top] at hI
    exact (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hB1t, hPt⟩, hDt⟩) hI
  have hIr := congrArg ENNReal.toReal hI
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hB1t, hPt⟩) hDt, ENNReal.toReal_add hB1t hPt,
    ENNReal.toReal_add hQt hB2t] at hIr
  have hDr : Dd.toReal ≤ -(∫ ζ, Ψ ζ ∂ν) - r := ENNReal.toReal_le_of_le_ofReal (by linarith) hDint
  have hΨI : ∫ ζ, Ψ ζ ∂ν = P.toReal - Q.toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hΨ]
  unfold extIntegral
  rw [← hB1, ← hB2, ← EReal.coe_ennreal_toReal hB1t, ← EReal.coe_ennreal_toReal hB2t,
    ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

end DRSOWWeakAux

open DRSOWass.Duality ModelRiskOT.Duality in
theorem solution {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤) :
    vP Ψ ν p θ = vD Ψ ν p θ ∧ vD Ψ ν p θ < ⊤ := by
  have hp0 : 0 < p := by linarith
  have hθp : 0 < θ ^ p := Real.rpow_pos_of_pos hθ p
  have hweak := DRSOWass.Duality.proposition_1 ν Ψ p θ hp hθ hΨm hΨ
  have hfin : vD Ψ ν p θ < ⊤ := by
    unfold growthRate at hκ
    obtain ⟨lam, hl⟩ := iInf_lt_iff.mp hκ
    obtain ⟨hlam, hl⟩ := iInf_lt_iff.mp hl
    obtain ⟨hbot, -⟩ := iInf_lt_iff.mp hl
    refine lt_of_le_of_lt (iInf₂_le lam hlam) ?_
    unfold dualObj
    exact EReal.add_lt_top (EReal.coe_ne_top _)
      (by rw [ne_eq, EReal.neg_eq_top_iff]; exact hbot.ne')
  refine ⟨le_antisymm hweak ?_, hfin⟩
  have h0 : Integrable (fun ζ : Ξ => dist (id ζ) ζ ^ p) ν := by
    simp only [id, dist_self, Real.zero_rpow hp0.ne']; exact integrable_const _
  have h0i : ∫ ζ, dist (id ζ) ζ ^ p ∂ν = 0 := by
    simp only [id, dist_self, Real.zero_rpow hp0.ne', integral_zero]
  have hid : ((∫ ζ, Ψ ζ ∂ν : ℝ) : EReal) ≤ vP Ψ ν p θ := by
    have := DRSOWWeakAux.mix_feasible ν Ψ hΨm p θ hp0 id id measurable_id measurable_id hΨ hΨ
      h0 h0 1 zero_le_one le_rfl (by rw [h0i]; simp only [mul_zero, add_zero]; exact hθp.le)
    simpa using this
  by_cases htop : vP Ψ ν p θ = ⊤
  · rw [htop]; exact le_top
  have hbot : vP Ψ ν p θ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hid
  obtain ⟨s, hs⟩ : ∃ s : ℝ, vP Ψ ν p θ = s := ⟨_, (EReal.coe_toReal htop hbot).symm⟩
  let Pr : ℝ → ℝ → Prop := fun c v => ∃ T : Ξ → Ξ, Measurable T ∧
    Integrable (fun ζ => Ψ (T ζ)) ν ∧ Integrable (fun ζ => dist (T ζ) ζ ^ p) ν ∧
    c = ∫ ζ, dist (T ζ) ζ ^ p ∂ν ∧ v = ∫ ζ, Ψ (T ζ) ∂ν
  have h0P : Pr 0 (∫ ζ, Ψ ζ ∂ν) := ⟨id, measurable_id, hΨ, h0, h0i.symm, rfl⟩
  have hmix : ∀ c1 v1 c2 v2 a, Pr c1 v1 → Pr c2 v2 → 0 ≤ a → a ≤ 1 →
      a * c1 + (1 - a) * c2 ≤ θ ^ p → a * v1 + (1 - a) * v2 ≤ s := by
    rintro c1 v1 c2 v2 a ⟨T1, m1, i1, j1, rfl, rfl⟩ ⟨T2, m2, i2, j2, rfl, rfl⟩ ha0 ha1 hc
    have := DRSOWWeakAux.mix_feasible ν Ψ hΨm p θ hp0 T1 T2 m1 m2 i1 i2 j1 j2 a ha0 ha1 hc
    rw [hs] at this; exact_mod_cast this
  obtain ⟨lam, hlam, hL⟩ := DRSOWWeakAux.lagrange Pr (θ ^ p) s _ hθp h0P hmix
  have H : ∀ T : Ξ → Ξ, Measurable T → Integrable (fun ζ => Ψ (T ζ)) ν →
      Integrable (fun ζ => dist (T ζ) ζ ^ p) ν →
      lam * θ ^ p - s ≤ ∫ ζ, (lam * dist (T ζ) ζ ^ p - Ψ (T ζ)) ∂ν := by
    intro T hT i1 i2
    have := hL _ _ ⟨T, hT, i1, i2, rfl, rfl⟩
    rw [integral_sub (i2.const_mul lam) i1, integral_const_mul]; linarith
  have hK := DRSOWWeakAux.key_B ν Ψ hΨm hΨ p hp0 lam (lam * θ ^ p - s) H
  refine (iInf₂_le lam hlam).trans ?_
  unfold dualObj
  rw [hs]
  calc ((lam * θ ^ p : ℝ) : EReal) - extIntegral ν (Phi Ψ p lam)
      ≤ ((lam * θ ^ p : ℝ) : EReal) - ((lam * θ ^ p - s : ℝ) : EReal) :=
        EReal.sub_le_sub le_rfl hK
    _ = (s : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
