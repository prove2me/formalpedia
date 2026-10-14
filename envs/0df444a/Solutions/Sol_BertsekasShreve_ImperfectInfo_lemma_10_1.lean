-- Prove2me | solution 1 for BertsekasShreve.ImperfectInfo.lemma_10_1
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:43:59.555859+00:00
-- url     : https://prove2.me/submissions/b129269f-be72-4beb-925a-3620ee5e02aa

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory


namespace BertsekasShreve.ImperfectInfo

namespace L101Cex
open scoped ENNReal

section HL
variable {X : ℕ → Type} {C : Type} [∀ j, MeasurableSpace (X j)] [MeasurableSpace C]

lemma hl0 (q : Measure (X 0)) (t : (j : ℕ) → Kernel (X j × C) (X (j + 1)))
    (μ : (n : ℕ) → Obs X C n → Measure C) :
    histLaw q t μ 0 = 0 ∨ (IsProbabilityMeasure (histLaw q t μ 0) ∧
      ∀ (A : Set (X 0)) (D : Set C), MeasurableSet A → MeasurableSet D →
        histLaw q t μ 0 {h | h.state ∈ A ∧ h.control ∈ D} = ∫⁻ y in A, μ 0 (Obs.init y) D ∂q) := by
  by_cases h : ∃ P : Measure (Hist X C 0), IsProbabilityMeasure P ∧
        ∀ (A : Set (X 0)) (D : Set C), MeasurableSet A → MeasurableSet D →
          P {h | h.state ∈ A ∧ h.control ∈ D} = ∫⁻ y in A, μ 0 (Obs.init y) D ∂q
  · right; rw [histLaw, dif_pos h]; exact h.choose_spec
  · left; rw [histLaw, dif_neg h]

lemma hl0_of (q : Measure (X 0)) (t : (j : ℕ) → Kernel (X j × C) (X (j + 1)))
    (μ : (n : ℕ) → Obs X C n → Measure C)
    (h : ∃ P : Measure (Hist X C 0), IsProbabilityMeasure P ∧
        ∀ (A : Set (X 0)) (D : Set C), MeasurableSet A → MeasurableSet D →
          P {h | h.state ∈ A ∧ h.control ∈ D} = ∫⁻ y in A, μ 0 (Obs.init y) D ∂q) :
    IsProbabilityMeasure (histLaw q t μ 0) ∧
      ∀ (A : Set (X 0)) (D : Set C), MeasurableSet A → MeasurableSet D →
        histLaw q t μ 0 {h | h.state ∈ A ∧ h.control ∈ D} = ∫⁻ y in A, μ 0 (Obs.init y) D ∂q := by
  rw [histLaw, dif_pos h]; exact h.choose_spec

lemma hlS (q : Measure (X 0)) (t : (j : ℕ) → Kernel (X j × C) (X (j + 1)))
    (μ : (n : ℕ) → Obs X C n → Measure C) (n : ℕ) :
    histLaw q t μ (n + 1) = 0 ∨ (IsProbabilityMeasure (histLaw q t μ (n + 1)) ∧
      ∀ (E : Set (Hist X C n)) (A : Set (X (n + 1))) (D : Set C),
          MeasurableSet E → MeasurableSet A → MeasurableSet D →
          histLaw q t μ (n + 1) {h | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
            ∫⁻ h in E, (∫⁻ y in A, μ (n + 1) (h.extend y) D ∂(t n (h.state, h.control)))
              ∂(histLaw q t μ n)) := by
  by_cases h : ∃ P : Measure (Hist X C (n + 1)), IsProbabilityMeasure P ∧
        ∀ (E : Set (Hist X C n)) (A : Set (X (n + 1))) (D : Set C),
          MeasurableSet E → MeasurableSet A → MeasurableSet D →
          P {h | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
            ∫⁻ h in E, (∫⁻ y in A, μ (n + 1) (h.extend y) D ∂(t n (h.state, h.control)))
              ∂(histLaw q t μ n)
  · right; rw [histLaw, dif_pos h]; exact h.choose_spec
  · left; rw [histLaw, dif_neg h]

lemma hlS_of (q : Measure (X 0)) (t : (j : ℕ) → Kernel (X j × C) (X (j + 1)))
    (μ : (n : ℕ) → Obs X C n → Measure C) (n : ℕ)
    (h : ∃ P : Measure (Hist X C (n + 1)), IsProbabilityMeasure P ∧
        ∀ (E : Set (Hist X C n)) (A : Set (X (n + 1))) (D : Set C),
          MeasurableSet E → MeasurableSet A → MeasurableSet D →
          P {h | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
            ∫⁻ h in E, (∫⁻ y in A, μ (n + 1) (h.extend y) D ∂(t n (h.state, h.control)))
              ∂(histLaw q t μ n)) :
    IsProbabilityMeasure (histLaw q t μ (n + 1)) ∧
      ∀ (E : Set (Hist X C n)) (A : Set (X (n + 1))) (D : Set C),
          MeasurableSet E → MeasurableSet A → MeasurableSet D →
          histLaw q t μ (n + 1) {h | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
            ∫⁻ h in E, (∫⁻ y in A, μ (n + 1) (h.extend y) D ∂(t n (h.state, h.control)))
              ∂(histLaw q t μ n) := by
  rw [histLaw, dif_pos h]; exact h.choose_spec

end HL

noncomputable def unif : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure unif := ⟨by
  simp [unif, ENNReal.inv_two_add_inv_two]⟩

lemma unif_single (b : Bool) : unif {b} = 2⁻¹ := by
  cases b <;> simp [unif]

lemma unif_ft : unif {false, true} = 1 := by
  rw [← measure_univ (μ := unif)]; congr 1; ext b; cases b <;> simp

lemma au (X : Type) [TopologicalSpace X] [PolishSpace X] : AnalyticSet (Set.univ : Set X) := by
  simpa using analyticSet_range_of_polishSpace (continuous_id (X := X))

lemma isB (X : Type) [TopologicalSpace X] [PolishSpace X] : IsBorelSpace X :=
  ⟨X, inferInstance, inferInstance, id, Topology.IsEmbedding.id, by
    rw [Set.range_id]; exact @MeasurableSet.univ _ (borel X)⟩

lemma lsa0 (X : Type) [TopologicalSpace X] [PolishSpace X] :
    LowerSemianalyticOn (fun _ : X => (0 : EReal)) Set.univ := by
  refine ⟨au X, fun c => ?_⟩
  by_cases h : (0 : EReal) < c
  · simpa [h] using au X
  · simpa [h] using (analyticSet_empty : AnalyticSet (∅ : Set X))

noncomputable def M : ISIModel Unit Unit Bool where
  N := 3
  N_pos := by norm_num
  α := 1
  α_pos := one_pos
  g := fun _ => 0
  t := Kernel.const _ (Measure.dirac ())
  s0 := Kernel.const _ unif
  s := Kernel.const _ unif
  U := fun _ _ => Set.univ
  borel_S := isB Unit
  borel_C := isB Unit
  borel_Z := isB Bool
  nonempty_S := ⟨()⟩
  nonempty_C := ⟨()⟩
  nonempty_Z := ⟨true⟩
  g_lsa := lsa0 _
  t_markov := inferInstance
  s0_markov := inferInstance
  s_markov := inferInstance
  U_nonempty := fun _ _ _ => Set.univ_nonempty
  Gamma_analytic := fun k _ => by
    have : GammaSet (fun (k : ℕ) (_ : Info Bool Unit k) => (Set.univ : Set Unit)) k = Set.univ := by
      ext; simp [GammaSet]
    rw [this]; exact au _

def idx (k : ℕ) : Fin (k + 1) := if k = 1 then Fin.last k else 0

def eta (k : ℕ) (pi : ProbabilityMeasure Unit × Info Bool Unit k) : Bool := pi.2.1 (idx k)

lemma step_apply (a : (Unit × Bool) × Unit) (A : Set (Unit × Bool)) (hA : MeasurableSet A) :
    M.stepKernel a A = unif (Prod.mk () ⁻¹' A) := by
  haveI : IsMarkovKernel M.s := M.s_markov
  haveI : IsMarkovKernel M.t := M.t_markov
  unfold ISIModel.stepKernel
  rw [Kernel.compProd_apply hA]
  simp [M, Kernel.comap_apply, Kernel.const_apply]

lemma step_apply' (a : (Unit × Bool) × Unit) (A : Set (Unit × Bool)) :
    M.stepKernel a A = unif (Prod.mk () ⁻¹' A) := step_apply a A MeasurableSet.of_discrete

abbrev H (n : ℕ) := Hist (fun _ => Unit × Bool) Unit n

lemma ct0 (π : (k : ℕ) → ProbabilityMeasure Unit × Info Bool Unit k → ProbabilityMeasure Unit)
    (p : ProbabilityMeasure Unit) (A : Set (Bool × Unit)) (B : Set Bool)
    (hB : MeasurableSet B) :
    M.law π p (0 + 1) {h | (eta 0 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∈ A ∧
        eta (0 + 1) (p, ISIModel.infoOf h.obs) ∈ B} =
      ∫⁻ h, A.indicator (fun yu => (Kernel.const (Bool × Unit) unif) yu B)
        (eta 0 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∂(M.law π p (0 + 1)) := by
  set E : Set (H 0) := {h | (eta 0 (p, ISIModel.infoOf h.obs), h.control) ∈ A} with hEdef
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have h1 : {h : H (0 + 1) | (eta 0 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∈ A ∧
      eta (0 + 1) (p, ISIModel.infoOf h.obs) ∈ B} =
      {h | h.prefix ∈ E ∧ h.state ∈ (Set.univ ×ˢ B) ∧ h.control ∈ Set.univ} := by
    ext h; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, and_true, E]; rfl
  have h2 : (fun h : H (0 + 1) => A.indicator (fun yu => (Kernel.const (Bool × Unit) unif) yu B)
      (eta 0 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control)) =
      {h : H (0 + 1) | h.prefix ∈ E ∧ h.state ∈ Set.univ ∧ h.control ∈ Set.univ}.indicator
        (fun _ => unif B) := by
    funext h
    by_cases hh : (eta 0 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∈ A <;>
      simp [Set.indicator, hh, E]
  rw [h1, h2, lintegral_indicator_const MeasurableSet.of_discrete]
  unfold ISIModel.law
  rcases hlS (X := fun _ => Unit × Bool) ((p : Measure Unit) ⊗ₘ M.s0) (fun _ => M.stepKernel)
    (fun n o => (π n (p, ISIModel.infoOf o) : Measure Unit)) 0 with h0 | ⟨_, hr⟩
  · rw [h0]; simp
  · rw [hr _ _ _ hE (MeasurableSet.univ.prod hB) MeasurableSet.univ,
      hr _ _ _ hE MeasurableSet.univ MeasurableSet.univ]
    simp [step_apply', unif_ft]

lemma ct1 (π : (k : ℕ) → ProbabilityMeasure Unit × Info Bool Unit k → ProbabilityMeasure Unit)
    (p : ProbabilityMeasure Unit) (A : Set (Bool × Unit)) (B : Set Bool)
    (hB : MeasurableSet B) :
    M.law π p (1 + 1) {h | (eta 1 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∈ A ∧
        eta (1 + 1) (p, ISIModel.infoOf h.obs) ∈ B} =
      ∫⁻ h, A.indicator (fun yu => (Kernel.const (Bool × Unit) unif) yu B)
        (eta 1 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∂(M.law π p (1 + 1)) := by
  set E : Set (H 1) := {h | (eta 1 (p, ISIModel.infoOf h.obs), h.control) ∈ A ∧ (h.1 0).2 ∈ B}
    with hEdef
  set E2 : Set (H 1) := {h | (eta 1 (p, ISIModel.infoOf h.obs), h.control) ∈ A} with hE2def
  have h1 : {h : H (1 + 1) | (eta 1 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∈ A ∧
      eta (1 + 1) (p, ISIModel.infoOf h.obs) ∈ B} =
      {h | h.prefix ∈ E ∧ h.state ∈ Set.univ ∧ h.control ∈ Set.univ} := by
    ext h; simp only [Set.mem_setOf_eq, Set.mem_univ, and_true, E]; rfl
  have h2 : (fun h : H (1 + 1) => A.indicator (fun yu => (Kernel.const (Bool × Unit) unif) yu B)
      (eta 1 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control)) =
      {h : H (1 + 1) | h.prefix ∈ E2 ∧ h.state ∈ Set.univ ∧ h.control ∈ Set.univ}.indicator
        (fun _ => unif B) := by
    funext h
    by_cases hh : (eta 1 (p, ISIModel.infoOf h.prefix.obs), h.prefix.control) ∈ A <;>
      simp [Set.indicator, hh, E2]
  rw [h1, h2, lintegral_indicator_const MeasurableSet.of_discrete]
  unfold ISIModel.law
  rcases hlS (X := fun _ => Unit × Bool) ((p : Measure Unit) ⊗ₘ M.s0) (fun _ => M.stepKernel)
    (fun n o => (π n (p, ISIModel.infoOf o) : Measure Unit)) 1 with h0 | ⟨_, hr⟩
  · rw [h0]; simp
  rw [hr _ _ _ MeasurableSet.of_discrete MeasurableSet.univ MeasurableSet.univ,
    hr _ _ _ MeasurableSet.of_discrete MeasurableSet.univ MeasurableSet.univ]
  simp only [measure_univ, setLIntegral_one, step_apply', Set.preimage_univ]
  set A1 : Set (Unit × Bool) := {xz | (xz.2, ()) ∈ A} with hA1
  set F : Set (H 0) := {h | (h.1 0).2 ∈ B} with hF
  have hE : E = {h | h.prefix ∈ F ∧ h.state ∈ A1 ∧ h.control ∈ Set.univ} := by
    ext h
    show (_ ∧ _) ↔ (_ ∧ _ ∧ _)
    exact ⟨fun ⟨a, b⟩ => ⟨b, a, trivial⟩, fun ⟨b, a, _⟩ => ⟨a, b⟩⟩
  have hE2 : E2 = {h | h.prefix ∈ Set.univ ∧ h.state ∈ A1 ∧ h.control ∈ Set.univ} := by
    ext h
    show _ ↔ (_ ∧ _ ∧ _)
    exact ⟨fun a => ⟨trivial, a, trivial⟩, fun ⟨_, a, _⟩ => a⟩
  rw [hE, hE2]
  rcases hlS (X := fun _ => Unit × Bool) ((p : Measure Unit) ⊗ₘ M.s0) (fun _ => M.stepKernel)
    (fun n o => (π n (p, ISIModel.infoOf o) : Measure Unit)) 0 with h0' | ⟨_, hr1⟩
  · rw [h0']; simp
  rw [hr1 _ _ _ MeasurableSet.of_discrete MeasurableSet.of_discrete MeasurableSet.univ,
    hr1 _ _ _ MeasurableSet.univ MeasurableSet.of_discrete MeasurableSet.univ]
  simp only [measure_univ, setLIntegral_one, step_apply']
  rw [setLIntegral_const, setLIntegral_const]
  have hF' : F = {h | h.state ∈ (Set.univ ×ˢ B) ∧ h.control ∈ Set.univ} := by
    ext h; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, and_true, F]; rfl
  rcases hl0 (X := fun _ => Unit × Bool) ((p : Measure Unit) ⊗ₘ M.s0) (fun _ => M.stepKernel)
    (fun n o => (π n (p, ISIModel.infoOf o) : Measure Unit)) with h00 | ⟨hP0, hr0⟩
  · rw [h00]; simp
  rw [hF', hr0 _ _ (MeasurableSet.univ.prod hB) MeasurableSet.univ]
  simp only [measure_univ, setLIntegral_one]
  haveI : IsMarkovKernel M.s0 := M.s0_markov
  rw [Measure.compProd_apply_prod MeasurableSet.univ hB]
  simp [M, Kernel.const_apply]
  ring

noncomputable def σ : SuffStat M (fun _ => Bool) where
  borel_Y := fun _ => inferInstance
  isBorel_Y := fun _ => isB Bool
  nonempty_Y := fun _ => ⟨true⟩
  η := eta
  η_measurable := fun k => (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  Γhat := fun _ => Set.univ
  Γhat_analytic := fun _ _ => au _
  Γhat_proj := fun _ _ => Set.image_univ_of_surjective Prod.fst_surjective
  Gamma_eq := fun k _ p => by ext q; simp [GammaSet, M]
  that := fun _ => Kernel.const _ unif
  that_markov := fun _ _ => inferInstance
  cond_trans := by
    intro k hk π _ p A B _ hB
    have hk' : k = 0 ∨ k = 1 := by
      have : k + 1 < 3 := hk
      omega
    rcases hk' with rfl | rfl
    · exact ct0 π p A B hB
    · exact ct1 π p A B hB
  ghat := fun _ _ => 0
  ghat_lsa := fun _ _ => lsa0 _
  cond_cost := fun _ _ _ _ _ _ _ _ => rfl

abbrev G (n : ℕ) := Hist (fun _ => Bool) Unit n

def f0 : Bool × Unit → G 0 := fun x => (fun _ => x.1, fun _ => x.2)

def fS (n : ℕ) : G n × (Bool × Unit) → G (n + 1) := fun x =>
  (Fin.snoc (α := fun _ => Bool) x.1.1 x.2.1, Fin.snoc (α := fun _ => Unit) x.1.2 x.2.2)

lemma ex0 (q : Measure Bool) [IsProbabilityMeasure q]
    (μ : (n : ℕ) → Obs (fun _ => Bool) Unit n → Measure Unit)
    (hμ : ∀ n o, μ n o = Measure.dirac ()) :
    ∃ P : Measure (G 0), IsProbabilityMeasure P ∧
      ∀ (A : Set Bool) (D : Set Unit), MeasurableSet A → MeasurableSet D →
        P {h | h.state ∈ A ∧ h.control ∈ D} = ∫⁻ y in A, μ 0 (Obs.init y) D ∂q := by
  refine ⟨(q.prod (Measure.dirac ())).map f0,
    Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable, fun A D hA hD => ?_⟩
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  have : f0 ⁻¹' {h : G 0 | h.state ∈ A ∧ h.control ∈ D} = A ×ˢ D := by ext x; rfl
  rw [this, Measure.prod_prod]
  simp only [hμ]
  rw [setLIntegral_const, mul_comm]

lemma exS (q : Measure Bool) (μ : (n : ℕ) → Obs (fun _ => Bool) Unit n → Measure Unit)
    (hμ : ∀ n o, μ n o = Measure.dirac ()) (n : ℕ)
    (hP : IsProbabilityMeasure (histLaw q (fun _ => Kernel.const _ unif) μ n)) :
    ∃ P : Measure (G (n + 1)), IsProbabilityMeasure P ∧
        ∀ (E : Set (G n)) (A : Set Bool) (D : Set Unit),
          MeasurableSet E → MeasurableSet A → MeasurableSet D →
          P {h | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
            ∫⁻ h in E, (∫⁻ y in A, μ (n + 1) (h.extend y) D
              ∂((fun j => Kernel.const (Bool × Unit) unif) n (h.state, h.control)))
              ∂(histLaw q (fun _ => Kernel.const _ unif) μ n) := by
  refine ⟨((histLaw q (fun _ => Kernel.const _ unif) μ n).prod
    (unif.prod (Measure.dirac ()))).map (fS n),
    Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable, fun E A D hE hA hD => ?_⟩
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  have : fS n ⁻¹' {h : G (n + 1) | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
      E ×ˢ (A ×ˢ D) := by
    ext ⟨h, y, u⟩
    simp [fS, Hist.prefix, Hist.state, Hist.control]
  rw [this, Measure.prod_prod, Measure.prod_prod]
  simp only [hμ, Kernel.const_apply]
  rw [setLIntegral_const, setLIntegral_const]
  ring

noncomputable def p₀ : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩

noncomputable def μ₀ : (k : ℕ) → (fun _ : ℕ => Bool) k → ProbabilityMeasure Unit :=
  fun _ _ => ⟨Measure.dirac (), inferInstance⟩

lemma hμ₀ : σ.IsMarkovPolicy μ₀ :=
  ⟨fun _ _ _ => measurable_const.nullMeasurable, fun k _ y => by simp [SuffStat.Uhat, σ, μ₀]⟩

def Bset : Set (G 2) := {h | h.1 0 = false ∧ h.1 2 = true}

lemma lhs_zero : M.law (σ.toISI μ₀) p₀ 2 (σ.V p₀ 2 ⁻¹' Bset) = 0 := by
  have : σ.V p₀ 2 ⁻¹' Bset = ∅ := by
    ext h
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    have e : (σ.V p₀ 2 h).1 0 = (σ.V p₀ 2 h).1 2 := rfl
    rw [e, h2] at h1
    exact Bool.noConfusion h1
  rw [this, measure_empty]

instance phi_prob : IsProbabilityMeasure (σ.phi p₀) := by
  haveI : IsMarkovKernel M.s0 := M.s0_markov
  unfold SuffStat.phi
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

lemma phi_false : σ.phi p₀ {false} = 2⁻¹ := by
  haveI : IsMarkovKernel M.s0 := M.s0_markov
  unfold SuffStat.phi
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  have : (fun xz : Unit × Bool => σ.η 0 (p₀, ((fun _ => xz.2), fun i => Fin.elim0 i))) ⁻¹'
      {false} = Set.univ ×ˢ {false} := by
    ext ⟨x, z⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_univ, true_and]
    rfl
  rw [this, Measure.compProd_apply_prod MeasurableSet.univ MeasurableSet.of_discrete]
  simp [M, Kernel.const_apply, unif_single, p₀]

lemma σ_that (k : ℕ) : σ.that k = Kernel.const _ unif := rfl

lemma rhs_ne : σ.lawHat (markovToPolicy μ₀) (σ.phi p₀) 2 Bset ≠ 0 := by
  unfold SuffStat.lawHat
  set μ := (fun n (o : Obs (fun _ => Bool) Unit n) => (markovToPolicy μ₀ n o : Measure Unit))
    with hμdef
  have hμ : ∀ n o, μ n o = Measure.dirac () := fun _ _ => rfl
  have P0 := hl0_of (σ.phi p₀) σ.that μ (ex0 _ μ hμ)
  have P1 := hlS_of (σ.phi p₀) σ.that μ 0 (exS _ μ hμ 0 P0.1)
  have P2 := hlS_of (σ.phi p₀) σ.that μ 1 (exS _ μ hμ 1 P1.1)
  have eB : Bset = {h : G (1 + 1) | h.prefix ∈ {h : G 1 | h.1 0 = false} ∧
      h.state ∈ ({true} : Set Bool) ∧ h.control ∈ Set.univ} := by
    ext h
    show (_ ∧ _) ↔ (_ ∧ _ ∧ _)
    exact ⟨fun ⟨a, b⟩ => ⟨a, b, trivial⟩, fun ⟨a, b, _⟩ => ⟨a, b⟩⟩
  have e1 : {h : G 1 | h.1 0 = false} = {h : G (0 + 1) | h.prefix ∈ {h : G 0 | h.1 0 = false} ∧
      h.state ∈ (Set.univ : Set Bool) ∧ h.control ∈ Set.univ} := by
    ext h
    show _ ↔ (_ ∧ _ ∧ _)
    exact ⟨fun a => ⟨a, trivial, trivial⟩, fun ⟨a, _, _⟩ => a⟩
  have e0 : {h : G 0 | h.1 0 = false} = {h : G 0 | h.state ∈ ({false} : Set Bool) ∧
      h.control ∈ Set.univ} := by
    ext h
    show _ ↔ (_ ∧ _)
    exact ⟨fun a => ⟨a, trivial⟩, fun ⟨a, _⟩ => a⟩
  rw [eB, P2.2 _ _ _ MeasurableSet.of_discrete MeasurableSet.of_discrete MeasurableSet.univ]
  simp only [hμ, measure_univ, setLIntegral_one, σ_that, Kernel.const_apply, setLIntegral_const]
  rw [e1,
    P1.2 _ _ _ MeasurableSet.of_discrete MeasurableSet.univ MeasurableSet.univ]
  simp only [hμ, measure_univ, setLIntegral_one, σ_that, Kernel.const_apply, setLIntegral_const]
  rw [e0, P0.2 _ _ MeasurableSet.of_discrete MeasurableSet.univ]
  simp only [hμ, measure_univ, setLIntegral_one, phi_false, unif_single]
  simp

theorem lemma_10_1_false : ¬ (∀ {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (p : ProbabilityMeasure S) (μ : (k : ℕ) → Y k → ProbabilityMeasure C)
    (hμ : σ.IsMarkovPolicy μ) (k : ℕ) (hk : k < M.N) (B : Set (Hist Y C k))
    (hB : MeasurableSet B),
    M.law (σ.toISI μ) p k (σ.V p k ⁻¹' B) = σ.lawHat (markovToPolicy μ) (σ.phi p) k B) := by
  intro H
  have := H (M := M) (Y := fun _ => Bool) σ p₀ μ₀ hμ₀ 2 (by show 2 < 3; norm_num) Bset
    MeasurableSet.of_discrete
  rw [lhs_zero] at this
  exact rhs_ne this.symm

end L101Cex
end BertsekasShreve.ImperfectInfo

open BertsekasShreve.ImperfectInfo


theorem solution : ¬ (∀ {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (p : ProbabilityMeasure S) (μ : (k : ℕ) → Y k → ProbabilityMeasure C)
    (hμ : σ.IsMarkovPolicy μ) (k : ℕ) (hk : k < M.N) (B : Set (Hist Y C k))
    (hB : MeasurableSet B),
    M.law (σ.toISI μ) p k (σ.V p k ⁻¹' B) = σ.lawHat (markovToPolicy μ) (σ.phi p) k B) := L101Cex.lemma_10_1_false
