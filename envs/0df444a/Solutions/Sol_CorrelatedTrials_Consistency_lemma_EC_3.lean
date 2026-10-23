-- Prove2me | solution 1 for CorrelatedTrials.Consistency.lemma_EC_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:36:22.408743+00:00
-- url     : https://prove2.me/submissions/a01acf52-af82-44b9-895f-93d44f42a62b

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess
import Theorems.Thm_CorrelatedTrials_Consistency_posterior_moments

open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace CtMat
open Matrix

variable {M : ℕ}

noncomputable def Step (lam : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ) (u : Fin M) :
    Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun j k => S j k - S j u * S u k / (lam u + S u u)

noncomputable def bf (S : Matrix (Fin M) (Fin M) ℝ) (x y : Fin M → ℝ) : ℝ := x ⬝ᵥ (S *ᵥ y)

lemma bf_symm {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (x y : Fin M → ℝ) :
    bf S x y = bf S y x := by
  unfold bf
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have : S.transpose = S := by simpa using hS.eq
  rw [this]

lemma bf_nonneg {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (x : Fin M → ℝ) : 0 ≤ bf S x x := by
  have := hS.posSemidef.dotProduct_mulVec_nonneg x
  simpa [bf] using this

lemma bf_cs {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (x y : Fin M → ℝ) :
    (bf S x y) ^ 2 ≤ bf S x x * bf S y y := by
  have hq : ∀ t : ℝ, 0 ≤ bf S y y * (t * t) + (2 * bf S x y) * t + bf S x x := by
    intro t
    have h := bf_nonneg hS (x + t • y)
    have e : bf S (x + t • y) (x + t • y) =
        bf S y y * (t * t) + (2 * bf S x y) * t + bf S x x := by
      have hs := bf_symm hS.1 y x
      simp only [bf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct,
        dotProduct_smul, smul_eq_mul] at hs ⊢
      rw [hs]; ring
    rw [← e]; exact h
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith


lemma bf_single {S : Matrix (Fin M) (Fin M) ℝ} (x : Fin M → ℝ) (u : Fin M) :
    bf S x (Pi.single u 1) = ∑ j, x j * S j u := by
  simp [bf, dotProduct, mulVec, Pi.single_apply]

lemma bf_step {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (lam : Fin M → ℝ) (u : Fin M)
    (x : Fin M → ℝ) :
    bf (Step lam S u) x x = bf S x x - (∑ j, x j * S j u) ^ 2 / (lam u + S u u) := by
  have hsym : ∀ a b, S a b = S b a := fun a b => by
    have := hS.apply b a
    simpa using this
  have h1 : ∀ k, S u k = S k u := fun k => hsym u k
  unfold bf Step
  simp only [dotProduct, mulVec, Matrix.of_apply]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
  congr 1
  simp only [h1]
  rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring


lemma sym_of {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (a b : Fin M) : S a b = S b a := by
  have := hS.apply b a
  simpa using this

lemma step_posDef {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) : (Step lam S u).PosDef := by
  have hsym := sym_of hS.1
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [Step, Matrix.of_apply, star_trivial]
    rw [hsym j i, hsym u j, hsym i u]
    ring
  · intro x hx
    have hpos := hS.dotProduct_mulVec_pos hx
    have hcs := bf_cs hS x (Pi.single u 1)
    rw [bf_single] at hcs
    have hee : bf S (Pi.single u 1) (Pi.single u 1) = S u u := by
      simp [bf, dotProduct, mulVec, Pi.single_apply]
    rw [hee] at hcs
    have hQ : 0 < bf S x x := by simpa [bf] using hpos
    have := bf_step hS.1 lam u x
    simp only [star_trivial]
    show 0 < bf (Step lam S u) x x
    rw [this]
    rw [sub_pos, div_lt_iff₀ hD]
    nlinarith [hcs, hQ, hu, hSuu]

lemma step_diag_le {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) (j : Fin M) : Step lam S u j j ≤ S j j := by
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  simp only [Step, Matrix.of_apply]
  rw [sym_of hS.1 u j, ← sq]
  have : 0 ≤ S j u ^ 2 / (lam u + S u u) := by positivity
  rw [sym_of hS.1 j u] at this ⊢
  linarith [this]

lemma step_diag_self {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) :
    1 / Step lam S u u u = 1 / S u u + 1 / lam u := by
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  simp only [Step, Matrix.of_apply]
  have h1 := hu.ne'
  have h2 := hSuu.ne'
  have h3 := hD.ne'
  have e : S u u - S u u * S u u / (lam u + S u u) = S u u * lam u / (lam u + S u u) := by
    field_simp; ring
  rw [e, one_div_div]
  field_simp

lemma step_cs {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (i j : Fin M) :
    (S i j) ^ 2 ≤ S i i * S j j := by
  have := bf_cs hS (Pi.single i 1) (Pi.single j 1)
  simpa [bf, dotProduct, mulVec, Pi.single_apply] using this

end CtMat

namespace CtSeq

variable {M : ℕ} (I : Instance M)

lemma sig_zero (ω : TrialSpace M) : Sig I 0 ω = I.Sig0 := rfl

lemma sig_succ (t : ℕ) (ω : TrialSpace M) :
    Sig I (t + 1) ω = CtMat.Step I.lam (Sig I t ω) (alloc I t ω) := by
  simp only [Sig, cpdeState, alloc, update, CtMat.Step]

lemma sig_posDef (t : ℕ) (ω : TrialSpace M) : (Sig I t ω).PosDef := by
  induction t with
  | zero => exact I.posDef
  | succ t ih =>
    rw [sig_succ]
    exact CtMat.step_posDef ih _ _ (I.lam_pos _)

lemma sig_diag_anti (t : ℕ) (ω : TrialSpace M) (j : Fin M) :
    Sig I (t + 1) ω j j ≤ Sig I t ω j j := by
  rw [sig_succ]
  exact CtMat.step_diag_le (sig_posDef I t ω) _ _ (I.lam_pos _) j

lemma sig_diag_le (t : ℕ) (ω : TrialSpace M) (j : Fin M) : Sig I t ω j j ≤ I.Sig0 j j := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (sig_diag_anti I t ω j).trans ih

lemma sig_inv (t : ℕ) (ω : TrialSpace M) (i : Fin M) :
    1 / Sig I t ω i i ≤ 1 / Sig I (t + 1) ω i i := by
  have h1 := sig_posDef I t ω
  have h2 : 0 < Sig I (t + 1) ω i i := (sig_posDef I (t + 1) ω).diag_pos
  exact one_div_le_one_div_of_le h2 (sig_diag_anti I t ω i)

lemma sig_inv_alloc (t : ℕ) (ω : TrialSpace M) (i : Fin M) (h : alloc I t ω = i) :
    1 / Sig I t ω i i + 1 / I.lam i ≤ 1 / Sig I (t + 1) ω i i := by
  rw [sig_succ, ← h]
  rw [CtMat.step_diag_self (sig_posDef I t ω) _ _ (I.lam_pos _)]

lemma part_a (ω : TrialSpace M) (i : Fin M) (hi : ∃ᶠ t in atTop, alloc I t ω = i) :
    Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) := by
  set g : ℕ → ℝ := fun t => 1 / Sig I t ω i i with hg
  have hmono : Monotone g := monotone_nat_of_le_succ (fun t => sig_inv I t ω i)
  have hl := I.lam_pos i
  have hex : ∀ k : ℕ, ∃ t, (k : ℝ) / I.lam i ≤ g t := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, ?_⟩
      have : 0 < g 0 := by
        have := (sig_posDef I 0 ω).diag_pos (i := i)
        simp only [hg]; positivity
      simpa using this.le
    | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', h1, h2⟩ := (hi.and_eventually (eventually_ge_atTop t)).exists
      refine ⟨t' + 1, ?_⟩
      have a := sig_inv_alloc I t' ω i h1
      have b := hmono h2
      have c : (((k + 1 : ℕ) : ℝ)) / I.lam i = (k : ℝ) / I.lam i + 1 / I.lam i := by
        push_cast; ring
      rw [c]
      simp only [hg] at b ⊢
      linarith
  have hT : Tendsto g atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone hmono (fun b => ?_)
    obtain ⟨t, ht⟩ := hex ⌈b * I.lam i⌉₊
    refine ⟨t, le_trans ?_ ht⟩
    rw [le_div_iff₀ hl]
    exact Nat.le_ceil _
  have := hT.inv_tendsto_atTop
  refine this.congr (fun t => ?_)
  simp [hg]

end CtSeq

namespace PostCons

variable {M : ℕ} (I : Instance M)

noncomputable def obs (T : ℕ) (ω : TrialSpace M) : Fin T → ℝ :=
  fun s => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω

noncomputable def F (T : ℕ) : MeasurableSpace (TrialSpace M) :=
  MeasurableSpace.comap (obs I T) inferInstance

lemma F_le (T : ℕ) : F I T ≤ (inferInstance : MeasurableSpace (TrialSpace M)) :=
  ((posterior_moments I T ⟨0, by have := I.two_le; omega⟩).1).comap_le

lemma F_mono {T T' : ℕ} (h : T ≤ T') : F I T ≤ F I T' := by
  have e : obs I T = (fun y : Fin T' → ℝ => fun s : Fin T => y (Fin.castLE h s)) ∘ obs I T' := by
    funext ω s; rfl
  unfold F
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))

noncomputable def filt : Filtration ℕ (inferInstance : MeasurableSpace (TrialSpace M)) where
  seq := F I
  mono' := fun _ _ h => F_mono I h
  le' := F_le I

instance : IsProbabilityMeasure (trialMeasure I) := by
  unfold trialMeasure; infer_instance

lemma theta_integrable (i : Fin M) : Integrable (fun ω => theta ω i) (trialMeasure I) := by
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin M) => x i)
      (multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0) := by
    have := (IsGaussian.integrable_id (μ := multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0))
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp this
  have hfst : (trialMeasure I).map Prod.fst = multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0 := by
    simp [trialMeasure]
  rw [← hfst] at h1
  exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).1 h1

end PostCons


namespace EC3Core

noncomputable abbrev G : Measure ℝ := gaussianReal 0 1

lemma G_Ici_pos (A : ℝ) : 0 < G (Set.Ici A) := by
  rw [pos_iff_ne_zero]
  intro h
  rw [G, gaussianReal_of_var_ne_zero _ one_ne_zero,
    withDensity_apply_eq_zero' (by fun_prop)] at h
  have : {x : ℝ | gaussianPDF 0 1 x ≠ 0} ∩ Set.Ici A = Set.Ici A := by
    ext x; simp [(gaussianPDF_pos 0 one_ne_zero x).ne']
  rw [this, Real.volume_Ici] at h
  exact ENNReal.top_ne_zero h

instance (s : ℝ) : IsProbabilityMeasure (auxMeasure s) := by
  unfold auxMeasure; infer_instance

lemma map_fst_aux (s : ℝ) : (auxMeasure s).map Prod.fst = gaussianReal 0 (Real.toNNReal s) := by
  unfold auxMeasure
  rw [Measure.map_fst_prod]; simp

lemma map_snd0_aux (s : ℝ) : (auxMeasure s).map (fun ω : AuxSpace => ω.2 0) = G := by
  have h1 : (auxMeasure s).map Prod.snd = Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 := by
    unfold auxMeasure
    rw [Measure.map_snd_prod]; simp
  have : (fun ω : AuxSpace => ω.2 0) = (fun w : ℕ → ℝ => w 0) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (by fun_prop) measurable_snd, h1]
  exact Measure.infinitePi_map_eval _ 0

lemma integral_fst (s : ℝ) : ∫ ω, ω.1 ∂(auxMeasure s) = 0 := by
  have := integral_map (μ := auxMeasure s) (φ := Prod.fst) (f := fun x => x) (by fun_prop)
    (by rw [map_fst_aux]; exact aestronglyMeasurable_id)
  rw [map_fst_aux, integral_id_gaussianReal] at this
  simpa using this.symm

lemma integral_snd0 (s : ℝ) : ∫ ω, ω.2 0 ∂(auxMeasure s) = 0 := by
  have := integral_map (μ := auxMeasure s) (φ := fun ω : AuxSpace => ω.2 0) (f := fun x => x)
    (by fun_prop) (by rw [map_snd0_aux]; exact aestronglyMeasurable_id)
  rw [map_snd0_aux, integral_id_gaussianReal] at this
  simpa using this.symm

lemma integrable_fst (s : ℝ) : Integrable (fun ω : AuxSpace => ω.1) (auxMeasure s) := by
  have : Integrable (fun x : ℝ => x) ((auxMeasure s).map Prod.fst) := by
    rw [map_fst_aux]; exact (memLp_id_gaussianReal 1).integrable le_rfl
  exact (integrable_map_measure (g := fun x : ℝ => x) aestronglyMeasurable_id
    (by fun_prop)).1 this

lemma integrable_snd0 (s : ℝ) : Integrable (fun ω : AuxSpace => ω.2 0) (auxMeasure s) := by
  have : Integrable (fun x : ℝ => x) ((auxMeasure s).map (fun ω : AuxSpace => ω.2 0)) := by
    rw [map_snd0_aux]; exact (memLp_id_gaussianReal 1).integrable le_rfl
  exact (integrable_map_measure (g := fun x : ℝ => x) aestronglyMeasurable_id
    (by fun_prop)).1 this

lemma Zproc_one (l s : ℝ) (ω : AuxSpace) :
    Zproc l s 1 ω = s * (ω.1 + Real.sqrt l * ω.2 0) / (l + s) := by
  simp [Zproc, auxSum, auxSample]

lemma integrable_Z (l s : ℝ) : Integrable (Zproc l s 1) (auxMeasure s) := by
  have : Zproc l s 1 = fun ω => (s / (l + s)) * ω.1 + (s * Real.sqrt l / (l + s)) * ω.2 0 := by
    funext ω; rw [Zproc_one]; ring
  rw [this]
  exact ((integrable_fst s).const_mul _).add ((integrable_snd0 s).const_mul _)

lemma integral_Z (l s : ℝ) : ∫ ω, Zproc l s 1 ω ∂(auxMeasure s) = 0 := by
  have : Zproc l s 1 = fun ω => (s / (l + s)) * ω.1 + (s * Real.sqrt l / (l + s)) * ω.2 0 := by
    funext ω; rw [Zproc_one]; ring
  rw [this, integral_add ((integrable_fst s).const_mul _) ((integrable_snd0 s).const_mul _),
    integral_const_mul, integral_const_mul, integral_fst, integral_snd0]
  simp

/-- The probability of the event `{a √s ≤ u ξ, 0 ≤ u ε₀}` for a sign `u`. -/
lemma prob_event (s : ℝ) (hs : 0 < s) (u : ℝ) (hu : u ^ 2 = 1) (a : ℝ) :
    auxMeasure s ({x : ℝ | a * Real.sqrt s ≤ u * x} ×ˢ {w : ℕ → ℝ | 0 ≤ u * w 0}) =
      G (Set.Ici a) * G (Set.Ici 0) := by
  unfold auxMeasure
  rw [Measure.prod_prod]
  congr 1
  · have hsq := Real.sqrt_pos.2 hs
    have hmap := gaussianReal_map_const_mul (μ := 0) (v := Real.toNNReal s) (u / Real.sqrt s)
    have hmap' : (gaussianReal 0 (Real.toNNReal s)).map ((u / Real.sqrt s) * ·) =
        gaussianReal 0 1 := by
      rw [hmap]; congr 1
      · simp
      · ext
        simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hs.le, NNReal.coe_one]
        rw [div_pow, Real.sq_sqrt hs.le, hu]; field_simp
    rw [G, ← hmap', Measure.map_apply (by fun_prop) measurableSet_Ici]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
  · have hmap := gaussianReal_map_const_mul (μ := 0) (v := 1) u
    have hmap' : (gaussianReal 0 1).map (u * ·) = gaussianReal 0 1 := by
      rw [hmap]; congr 1
      · simp
      · ext; simp [hu]
    have e : {w : ℕ → ℝ | 0 ≤ u * w 0} = (fun w : ℕ → ℝ => u * w 0) ⁻¹' Set.Ici 0 := rfl
    rw [e, ← Measure.map_apply (by fun_prop) measurableSet_Ici]
    have : (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map (fun w : ℕ → ℝ => u * w 0) =
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map (fun w : ℕ → ℝ => w 0)).map
          (u * ·) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
    rw [this, Measure.infinitePi_map_eval, hmap']

namespace CtCore
section terminal
variable {M : ℕ} (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)

/-- the Lipschitz-type constant -/
noncomputable def Kc : ℝ := ∑ j, |Sig i j / Sig i i|

lemma Kc_nonneg : 0 ≤ Kc Sig i := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma terminal_le (z : ℝ) : terminal mu Sig i z ≤ maxMean mu i + Kc Sig i * |z| := by
  unfold terminal
  refine Finset.sup'_le _ _ (fun j _ => ?_)
  have h1 : mu j ≤ maxMean mu i := Finset.le_sup' mu (Finset.mem_univ j)
  have h2 : |Sig i j / Sig i i| ≤ Kc Sig i :=
    Finset.single_le_sum (f := fun j => |Sig i j / Sig i i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h3 : Sig i j / Sig i i * z ≤ |Sig i j / Sig i i| * |z| := by
    rw [← abs_mul]; exact le_abs_self _
  nlinarith [abs_nonneg z]

lemma terminal_ge (z : ℝ) : mu i - Kc Sig i * |z| ≤ terminal mu Sig i z := by
  have h1 : mu i + Sig i i / Sig i i * z ≤ terminal mu Sig i z := by
    unfold terminal
    exact Finset.le_sup' (fun j => mu j + Sig i j / Sig i i * z) (Finset.mem_univ i)
  have h2 : |Sig i i / Sig i i| ≤ Kc Sig i :=
    Finset.single_le_sum (f := fun j => |Sig i j / Sig i i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h3 : -(|Sig i i / Sig i i| * |z|) ≤ Sig i i / Sig i i * z := by
    rw [← abs_mul]; exact neg_abs_le _
  nlinarith [abs_nonneg z]

lemma terminal_meas : Measurable (terminal mu Sig i) := by
  unfold terminal
  have := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin M)))
    ⟨i, Finset.mem_univ i⟩ (f := fun j (z : ℝ) => mu j + Sig i j / Sig i i * z) (fun j _ => by fun_prop)
  convert this using 1
  funext z
  exact (Finset.sup'_apply (s := Finset.univ) (H := ⟨i, Finset.mem_univ i⟩) (f := fun j (z : ℝ) => mu j + Sig i j / Sig i i * z) z).symm

end terminal


section main
variable {M : ℕ} (lam c : Fin M → ℝ) (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)

lemma integrable_terminal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Zt : Ω → ℝ} (hZ : Integrable Zt P) :
    Integrable (fun ω => terminal mu Sig i (Zt ω)) P := by
  refine Integrable.mono' (g := fun ω => (|maxMean mu i| + |mu i|) + Kc Sig i * |Zt ω|)
    ((integrable_const _).add (hZ.abs.const_mul _))
    ((terminal_meas mu Sig i).comp_aemeasurable hZ.1.aemeasurable).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have h1 := terminal_le mu Sig i (Zt ω)
  have h2 := terminal_ge mu Sig i (Zt ω)
  rw [Real.norm_eq_abs, abs_le]
  have := le_abs_self (maxMean mu i)
  have := neg_abs_le (mu i)
  constructor <;> nlinarith [abs_nonneg (maxMean mu i), abs_nonneg (mu i), le_abs_self (mu i),
    neg_abs_le (maxMean mu i), mul_nonneg (Kc_nonneg Sig i) (abs_nonneg (Zt ω))]
end main
end CtCore

end EC3Core

namespace EC3Core
open CtCore

lemma gain {M : ℕ} (lam c : Fin M → ℝ) (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (i : Fin M) (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i)
    (m k : Fin M) (hm : mu m = maxMean mu i) (K a : ℝ) (hK : |mu k - mu m| + 1 ≤ K)
    (hβ : Sig i k / Sig i i - Sig i m / Sig i i ≠ 0)
    (ha : K * (lam i + Sig i i) ≤
      a * |Sig i k / Sig i i - Sig i m / Sig i i| * (Sig i i * Real.sqrt (Sig i i))) :
    -1 + (1 / c i) * (G (Set.Ici a) * G (Set.Ici 0)).toReal ≤ nuCKG1 lam c mu Sig i := by
  set l := lam i with hl_def
  set s := Sig i i with hs_def
  set β := Sig i k / s - Sig i m / s with hβ_def
  set d := mu k - mu m with hd_def
  set u := β / |β| with hu_def
  have habs : 0 < |β| := abs_pos.2 hβ
  have hβu : β = |β| * u := by rw [hu_def]; field_simp
  have hu2 : u ^ 2 = 1 := by rw [hu_def, div_pow, sq_abs]; field_simp
  set Z := Zproc l s 1 with hZ_def
  have hZint : Integrable Z (auxMeasure s) := integrable_Z l s
  set E : Set AuxSpace := {x : ℝ | a * Real.sqrt s ≤ u * x} ×ˢ {w : ℕ → ℝ | 0 ≤ u * w 0}
    with hE_def
  have hEm : MeasurableSet E := by
    refine MeasurableSet.prod ?_ ?_
    · exact measurableSet_le (by fun_prop) (by fun_prop)
    · exact measurableSet_le (by fun_prop) (by fun_prop)
  -- pointwise lower bound of the terminal reward
  have hpt : ∀ ω, mu m + Sig i m / s * Z ω + max (d + β * Z ω) 0 ≤ terminal mu Sig i (Z ω) := by
    intro ω
    have h1 : mu m + Sig i m / s * Z ω ≤ terminal mu Sig i (Z ω) := by
      unfold terminal
      exact Finset.le_sup' (fun j => mu j + Sig i j / Sig i i * Z ω) (Finset.mem_univ m)
    have h2 : mu k + Sig i k / s * Z ω ≤ terminal mu Sig i (Z ω) := by
      unfold terminal
      exact Finset.le_sup' (fun j => mu j + Sig i j / Sig i i * Z ω) (Finset.mem_univ k)
    rcases le_total (d + β * Z ω) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; rw [hd_def, hβ_def] at *; linarith
  -- on E the gain is at least one
  have hE1 : ∀ ω ∈ E, 1 ≤ max (d + β * Z ω) 0 := by
    rintro ω ⟨h1, h2⟩
    simp only [Set.mem_setOf_eq] at h1 h2
    have hsq := Real.sqrt_pos.2 hs
    have hls : 0 < l + s := by linarith
    have hZ : u * Z ω * (l + s) = s * (u * ω.1 + Real.sqrt l * (u * ω.2 0)) := by
      rw [hZ_def, Zproc_one]; field_simp
    have hlow : s * (a * Real.sqrt s) ≤ u * Z ω * (l + s) := by
      rw [hZ]
      have : 0 ≤ Real.sqrt l * (u * ω.2 0) := mul_nonneg (Real.sqrt_nonneg _) h2
      nlinarith
    have hβZ : K ≤ β * Z ω := by
      rw [hβu]
      have e1 : |β| * u * Z ω * (l + s) = |β| * (u * Z ω * (l + s)) := by ring
      have : K * (l + s) ≤ |β| * u * Z ω * (l + s) := by
        rw [e1]
        calc K * (l + s) ≤ a * |β| * (s * Real.sqrt s) := ha
          _ = |β| * (s * (a * Real.sqrt s)) := by ring
          _ ≤ |β| * (u * Z ω * (l + s)) := mul_le_mul_of_nonneg_left hlow habs.le
      exact le_of_mul_le_mul_right this hls
    have : -|d| ≤ d := neg_abs_le d
    exact le_trans (by linarith) (le_max_left _ _)
  have hmaxint : Integrable (fun ω => max (d + β * Z ω) 0) (auxMeasure s) :=
    ((integrable_const d).add (hZint.const_mul β)).pos_part
  have hind : ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂(auxMeasure s) ≤
      ∫ ω, max (d + β * Z ω) 0 ∂(auxMeasure s) := by
    refine integral_mono ((integrable_const 1).indicator hEm) hmaxint (fun ω => ?_)
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]; exact hE1 ω hω
    · rw [Set.indicator_of_notMem hω]; exact le_max_right _ _
  have hPE : auxMeasure s E = G (Set.Ici a) * G (Set.Ici 0) := prob_event s hs u hu2 a
  rw [integral_indicator_const _ hEm, smul_eq_mul, mul_one, measureReal_def, hPE] at hind
  have hlin : ∫ ω, (mu m + Sig i m / s * Z ω + max (d + β * Z ω) 0) ∂(auxMeasure s) =
      mu m + ∫ ω, max (d + β * Z ω) 0 ∂(auxMeasure s) := by
    have hA : Integrable (fun ω => mu m + Sig i m / s * Z ω) (auxMeasure s) :=
      (integrable_const _).add (hZint.const_mul _)
    have hB : Integrable (fun ω => Sig i m / s * Z ω) (auxMeasure s) := hZint.const_mul _
    rw [integral_add hA hmaxint, integral_add (integrable_const _) hB, integral_const_mul,
      integral_const]
    rw [hZ_def, integral_Z]; simp
  have hAll : Integrable (fun ω => mu m + Sig i m / s * Z ω + max (d + β * Z ω) 0)
      (auxMeasure s) := ((integrable_const _).add (hZint.const_mul _)).add hmaxint
  have hterm := integral_mono hAll (integrable_terminal mu Sig i hZint) hpt
  rw [hlin] at hterm
  unfold nuCKG1
  rw [← hm]
  have hc' : 0 < 1 / c i := by positivity
  have : (G (Set.Ici a) * G (Set.Ici 0)).toReal ≤
      ∫ ω, terminal mu Sig i (Zproc (lam i) (Sig i i) 1 ω) ∂(auxMeasure (Sig i i)) - mu m := by
    linarith
  nlinarith
end EC3Core


namespace EC3Core
open CtCore

lemma pathwise {M : ℕ} (I : Instance M) (ω : TrialSpace M) (B : ℝ)
    (hB : ∀ T j, |mu I T ω j| ≤ B) (i : Fin M)
    (hyp : ∀ ε > 0, ∃ᶠ T in atTop, nuCKG1 I.lam I.c (mu I T ω) (Sig I T ω) i < -1 + ε) :
    Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) := by
  by_contra hnot
  have hpos : ∀ T, 0 < Sig I T ω i i := fun T => (CtSeq.sig_posDef I T ω).diag_pos
  have hanti : Antitone (fun T => Sig I T ω i i) :=
    antitone_nat_of_succ_le (fun T => CtSeq.sig_diag_anti I T ω i)
  obtain ⟨s0, hs0, hs0T⟩ : ∃ s0 > 0, ∀ T, s0 ≤ Sig I T ω i i := by
    by_contra hc
    push_neg at hc
    apply hnot
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T0, hT0⟩ := hc ε hε
    refine ⟨T0, fun T hT => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (hpos T)]
    exact lt_of_le_of_lt (hanti hT) hT0
  -- some arm is sampled infinitely often
  obtain ⟨j, hj⟩ : ∃ j, ∃ᶠ t in atTop, alloc I t ω = j := by
    by_contra hc
    push_neg at hc
    have : ∀ᶠ t in atTop, ∀ j, alloc I t ω ≠ j := by
      rw [eventually_all]
      intro j
      have := hc j
      simpa [Filter.Frequently] using this
    obtain ⟨t, ht⟩ := this.exists
    exact ht _ rfl
  have hjj := CtSeq.part_a I ω j hj
  have hev : ∀ᶠ T in atTop, Sig I T ω j j ≤ s0 / 16 :=
    hjj.eventually (eventually_le_nhds (by linarith))
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 i)
  set l := I.lam i
  have hl : 0 < l := I.lam_pos i
  set S0 := I.Sig0 i i
  set K := 2 * B + 1
  set A := K * (l + S0) * 4 / (s0 * Real.sqrt s0)
  set q := (G (Set.Ici A) * G (Set.Ici 0)).toReal
  have hq : 0 < q := by
    refine ENNReal.toReal_pos (mul_ne_zero (G_Ici_pos A).ne' (G_Ici_pos 0).ne') ?_
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hc := I.c_pos i
  have hgain : ∀ᶠ T in atTop, -1 + (1 / I.c i) * q ≤ nuCKG1 I.lam I.c (mu I T ω) (Sig I T ω) i := by
    filter_upwards [hev] with T hT
    set Sg := Sig I T ω
    set μT := mu I T ω
    have hs := hpos T
    have hPD := CtSeq.sig_posDef I T ω
    -- |r_j| ≤ 1/4
    have hrj : |Sg i j / Sg i i| ≤ 1 / 4 := by
      have hcs := CtMat.step_cs hPD i j
      have h1 : (Sg i j / Sg i i) ^ 2 ≤ 1 / 16 := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        have : Sg i i * Sg j j ≤ Sg i i ^ 2 / 16 := by
          have := hs0T T
          have hjj' : Sg j j ≤ s0 / 16 := hT
          nlinarith
        linarith
      nlinarith [abs_nonneg (Sg i j / Sg i i), sq_abs (Sg i j / Sg i i)]
    obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' (⟨i, Finset.mem_univ i⟩ :
      (Finset.univ : Finset (Fin M)).Nonempty) μT
    have hm' : μT m = maxMean μT i := hm.symm
    have hrii : Sg i i / Sg i i = 1 := div_self hs.ne'
    obtain ⟨k, hk⟩ : ∃ k, 1 / 4 ≤ |Sg i k / Sg i i - Sg i m / Sg i i| := by
      by_cases h : 1 / 2 ≤ |Sg i i / Sg i i - Sg i m / Sg i i|
      · exact ⟨i, by linarith⟩
      · refine ⟨j, ?_⟩
        push_neg at h
        rw [hrii] at h
        have := abs_sub_abs_le_abs_sub (1 - Sg i m / Sg i i) (Sg i j / Sg i i - Sg i m / Sg i i)
        have e : (1 - Sg i m / Sg i i) - (Sg i j / Sg i i - Sg i m / Sg i i) = 1 - Sg i j / Sg i i := by
          ring
        rw [e] at this
        have h3 : 3 / 4 ≤ |1 - Sg i j / Sg i i| := by
          have := abs_sub_abs_le_abs_sub (1 : ℝ) (Sg i j / Sg i i)
          rw [abs_one] at this; linarith
        rw [abs_le] at hrj
        have := abs_sub_abs_le_abs_sub (1 - Sg i j / Sg i i) (1 - Sg i m / Sg i i)
        have e2 : (1 - Sg i j / Sg i i) - (1 - Sg i m / Sg i i) =
            -(Sg i j / Sg i i - Sg i m / Sg i i) := by ring
        rw [e2, abs_neg] at this
        linarith
    have hβ : Sg i k / Sg i i - Sg i m / Sg i i ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hk; linarith
    have hK : |μT k - μT m| + 1 ≤ K := by
      have h1 := hB T k
      have h2 := hB T m
      have := abs_sub (μT k) (μT m)
      linarith
    have hsS : Sg i i ≤ S0 := CtSeq.sig_diag_le I T ω i
    have hsq0 : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
    have hsq : Real.sqrt s0 ≤ Real.sqrt (Sg i i) := Real.sqrt_le_sqrt (hs0T T)
    have ha : K * (l + Sg i i) ≤
        A * |Sg i k / Sg i i - Sg i m / Sg i i| * (Sg i i * Real.sqrt (Sg i i)) := by
      have hK0 : 0 < K := by simp only [K]; linarith
      have hS0 : 0 < S0 := I.posDef.diag_pos
      have hA0 : 0 ≤ A := by
        simp only [A]
        exact div_nonneg (mul_nonneg (mul_nonneg hK0.le (by linarith)) (by norm_num))
          (by positivity)
      have e : A * (1 / 4) * (s0 * Real.sqrt s0) = K * (l + S0) := by
        simp only [A]; field_simp
      have h1 : K * (l + Sg i i) ≤ K * (l + S0) := by nlinarith
      have h2 : s0 * Real.sqrt s0 ≤ Sg i i * Real.sqrt (Sg i i) :=
        mul_le_mul (hs0T T) hsq hsq0.le hs.le
      have h3 : A * (1 / 4) * (s0 * Real.sqrt s0) ≤
          A * |Sg i k / Sg i i - Sg i m / Sg i i| * (Sg i i * Real.sqrt (Sg i i)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hk hA0) h2 (by positivity) (by positivity)
      linarith
    exact gain I.lam I.c μT Sg i hl hs hc m k hm' K A hK hβ ha
  have hε : 0 < (1 / I.c i) * q := by positivity
  obtain ⟨T, h1, h2⟩ := ((hyp _ hε).and_eventually hgain).exists
  linarith

end EC3Core

open EC3Core PostCons in
theorem solution {M : ℕ} (I : Instance M) :
    ∀ᵐ ω ∂(trialMeasure I),
      (∀ i, ∀ ε > 0, ∃ᶠ T in atTop, nuCKG1 I.lam I.c (mu I T ω) (Sig I T ω) i < -1 + ε) →
        ∀ i, Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) := by
  set P := trialMeasure I
  -- each posterior mean converges almost surely (martingale convergence)
  have hconv : ∀ j, ∀ᵐ ω ∂P, ∃ L, Tendsto (fun T => mu I T ω j) atTop (𝓝 L) := by
    intro j
    have hθ := theta_integrable I j
    have hunif : UniformIntegrable (fun n => P[fun ω => theta ω j | filt I n]) 1 P :=
      hθ.uniformIntegrable_condExp_filtration
    obtain ⟨R, hR⟩ := hunif.2.2
    have hlim := (martingale_condExp (fun ω => theta ω j) (filt I) P).submartingale.ae_tendsto_limitProcess hR
    have hce : ∀ᵐ ω ∂P, ∀ T, mu I T ω j = (P[fun ω => theta ω j | filt I T]) ω :=
      ae_all_iff.2 fun T => (posterior_moments I T j).2.2.2.1
    filter_upwards [hlim, hce] with ω h1 h2
    exact ⟨_, h1.congr fun T => (h2 T).symm⟩
  filter_upwards [ae_all_iff.2 hconv] with ω hω hyp i
  have hbd : ∀ j, ∃ C, ∀ T, |mu I T ω j| ≤ C := by
    intro j
    obtain ⟨L, hL⟩ := hω j
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hL)
    exact ⟨C, fun T => by simpa [Real.norm_eq_abs] using hC _ ⟨T, rfl⟩⟩
  choose C hC using hbd
  refine pathwise I ω (∑ j, |C j|) (fun T j => ?_) i (hyp i)
  calc |mu I T ω j| ≤ C j := hC j T
    _ ≤ |C j| := le_abs_self _
    _ ≤ ∑ j, |C j| := Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
