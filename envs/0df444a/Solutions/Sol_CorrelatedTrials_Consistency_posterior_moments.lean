-- Prove2me | solution 1 for CorrelatedTrials.Consistency.posterior_moments
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:01:45.380235+00:00
-- url     : https://prove2.me/submissions/67e9c9ff-573c-4788-93bb-b3923cec6200

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace CtCore

noncomputable abbrev nu : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

instance (s : ℝ) : IsProbabilityMeasure (auxMeasure s) := by
  unfold auxMeasure; infer_instance

lemma map_snd_aux (s : ℝ) : (auxMeasure s).map Prod.snd = nu := by
  unfold auxMeasure nu
  rw [Measure.map_snd_prod]; simp

lemma map_fst_aux (s : ℝ) : (auxMeasure s).map Prod.fst = gaussianReal 0 (Real.toNNReal s) := by
  unfold auxMeasure
  rw [Measure.map_fst_prod]; simp

lemma gl_xi (s : ℝ) : HasGaussianLaw (fun ω : AuxSpace => ω.1) (auxMeasure s) where
  isGaussian_map := by
    show IsGaussian ((auxMeasure s).map Prod.fst)
    rw [map_fst_aux]; infer_instance

lemma gl_nu_eval (i : ℕ) : HasGaussianLaw (fun ω : ℕ → ℝ => ω i) nu where
  isGaussian_map := by
    have := Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) i
    show IsGaussian (nu.map (fun ω : ℕ → ℝ => ω i))
    rw [show nu.map (fun ω : ℕ → ℝ => ω i) = gaussianReal 0 1 from this]; infer_instance

lemma iindep_nu : iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) => ω i) nu :=
  iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => x) (fun _ => measurable_id)

lemma gl_eps (s : ℝ) (N : ℕ) : HasGaussianLaw (fun (ω : AuxSpace) (r : Fin N) => ω.2 r) (auxMeasure s) where
  isGaussian_map := by
    have h1 : HasGaussianLaw (fun (ω : ℕ → ℝ) (r : Fin N) => ω r) nu :=
      iIndepFun.hasGaussianLaw (fun r => gl_nu_eval r) (iindep_nu.precomp (g := fun r : Fin N => (r : ℕ)) Fin.val_injective)
    have := h1.isGaussian_map
    have e : (auxMeasure s).map (fun (ω : AuxSpace) (r : Fin N) => ω.2 r) =
        nu.map (fun (ω : ℕ → ℝ) (r : Fin N) => ω r) := by
      rw [← map_snd_aux s, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [e]; exact this


noncomputable def Yc {N : ℕ} : Option (Fin N) → AuxSpace → ℝ
  | none, ω => ω.1
  | some r, ω => ω.2 r

noncomputable def lf {N : ℕ} (c : Option (Fin N) → ℝ) (ω : AuxSpace) : ℝ := ∑ j, c j * Yc j ω

noncomputable def wt {N : ℕ} (s : ℝ) : Option (Fin N) → ℝ
  | none => s
  | some _ => 1

lemma indep_xi_eps (s : ℝ) (N : ℕ) :
    IndepFun (fun ω : AuxSpace => ω.1) (fun (ω : AuxSpace) (r : Fin N) => ω.2 r) (auxMeasure s) :=
  indepFun_prod (X := fun x : ℝ => x) (Y := fun (w : ℕ → ℝ) (r : Fin N) => w r)
    measurable_id (by fun_prop)

lemma gl_pair (s : ℝ) (N : ℕ) :
    HasGaussianLaw (fun ω : AuxSpace => (ω.1, fun r : Fin N => ω.2 r)) (auxMeasure s) :=
  IndepFun.hasGaussianLaw (gl_xi s) (gl_eps s N) (indep_xi_eps s N)

lemma gl_Y (s : ℝ) (N : ℕ) :
    HasGaussianLaw (fun (ω : AuxSpace) (j : Option (Fin N)) => Yc j ω) (auxMeasure s) := by
  let T : ℝ × (Fin N → ℝ) →L[ℝ] (Option (Fin N) → ℝ) :=
    ContinuousLinearMap.pi (fun j : Option (Fin N) =>
      match j with
      | none => ContinuousLinearMap.fst ℝ ℝ (Fin N → ℝ)
      | some r => (ContinuousLinearMap.proj r).comp (ContinuousLinearMap.snd ℝ ℝ (Fin N → ℝ)))
  have := (gl_pair s N).map T
  have e : (fun (ω : AuxSpace) (j : Option (Fin N)) => Yc j ω) =
      T ∘ (fun ω : AuxSpace => (ω.1, fun r : Fin N => ω.2 r)) := by
    funext ω j
    cases j <;> simp [T, Yc]
  rw [e]; exact this

lemma memLp_Yc (s : ℝ) {N : ℕ} (j : Option (Fin N)) : MemLp (Yc j) 2 (auxMeasure s) :=
  ((gl_Y s N).eval j).memLp_two

lemma cov_xi_eps (s : ℝ) {N : ℕ} (r : Fin N) :
    cov[Yc (none : Option (Fin N)), Yc (some r); auxMeasure s] = 0 := by
  have h1 : MemLp (fun ω : ℝ × (ℕ → ℝ) => ω.1) 2 ((gaussianReal 0 (Real.toNNReal s)).prod nu) :=
    memLp_Yc s (N := N) none
  have h2 : MemLp (fun ω : ℝ × (ℕ → ℝ) => ω.2 r) 2 ((gaussianReal 0 (Real.toNNReal s)).prod nu) :=
    memLp_Yc s (some r)
  exact (indepFun_prod (X := fun x : ℝ => x) (Y := fun (w : ℕ → ℝ) => w r)
    (μ := gaussianReal 0 (Real.toNNReal s)) (ν := nu) measurable_id (by fun_prop)).covariance_eq_zero h1 h2

lemma cov_eps_eps (s : ℝ) {N : ℕ} (r q : Fin N) (h : r ≠ q) :
    cov[Yc (some r), Yc (some q); auxMeasure s] = 0 := by
  have e := covariance_map (μ := auxMeasure s) (Z := Prod.snd)
    (X := fun w : ℕ → ℝ => w r) (Y := fun w : ℕ → ℝ => w q)
    (by rw [map_snd_aux]; exact (measurable_pi_apply _).aestronglyMeasurable) (by rw [map_snd_aux]; exact (measurable_pi_apply _).aestronglyMeasurable) (by fun_prop)
  rw [map_snd_aux] at e
  have h0 : cov[fun w : ℕ → ℝ => w r, fun w : ℕ → ℝ => w q; nu] = 0 :=
    (iindep_nu.indepFun (i := (r : ℕ)) (j := (q : ℕ)) (fun hh => h (Fin.ext hh))).covariance_eq_zero
      (gl_nu_eval r).memLp_two (gl_nu_eval q).memLp_two
  rw [h0] at e
  exact e.symm

lemma cov_Yc_ne (s : ℝ) {N : ℕ} (j k : Option (Fin N)) (h : j ≠ k) :
    cov[Yc j, Yc k; auxMeasure s] = 0 := by
  cases j with
  | none =>
    cases k with
    | none => exact absurd rfl h
    | some r => exact cov_xi_eps s r
  | some r =>
    cases k with
    | none => rw [covariance_comm]; exact cov_xi_eps s r
    | some q => exact cov_eps_eps s r q (fun hh => h (by rw [hh]))


lemma cov_Yc_self (s : ℝ) (hs : 0 ≤ s) {N : ℕ} (j : Option (Fin N)) :
    cov[Yc j, Yc j; auxMeasure s] = wt s j := by
  rw [covariance_self (memLp_Yc s j).aemeasurable]
  cases j with
  | none =>
    have := variance_map (μ := auxMeasure s) (X := id) (Y := Prod.fst)
      (by rw [map_fst_aux]; exact aemeasurable_id) (by fun_prop)
    rw [map_fst_aux, variance_id_gaussianReal] at this
    simp only [wt, Real.coe_toNNReal _ hs] at this ⊢
    exact this.symm
  | some r =>
    have := variance_map (μ := auxMeasure s) (X := fun w : ℕ → ℝ => w r) (Y := Prod.snd)
      (by rw [map_snd_aux]; exact (measurable_pi_apply _).aemeasurable) (by fun_prop)
    rw [map_snd_aux] at this
    have h2 : Var[fun w : ℕ → ℝ => w r; nu] = 1 := by
      have := variance_map (μ := nu) (X := id) (Y := fun w : ℕ → ℝ => w r)
        (by rw [show nu.map (fun w : ℕ → ℝ => w r) = gaussianReal 0 1 from
              Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) r]; exact aemeasurable_id)
        (measurable_pi_apply _).aemeasurable
      rw [show nu.map (fun w : ℕ → ℝ => w r) = gaussianReal 0 1 from
              Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) r,
          variance_id_gaussianReal] at this
      simpa using this.symm
    simp only [wt]
    rw [← h2]; exact this.symm

lemma lin_cov (s : ℝ) (hs : 0 ≤ s) {N : ℕ} (c d : Option (Fin N) → ℝ) :
    cov[lf c, lf d; auxMeasure s] = ∑ j, c j * d j * wt s j := by
  unfold lf
  rw [covariance_fun_sum_fun_sum (fun i => (memLp_Yc s i).const_mul (c i))
    (fun i => (memLp_Yc s i).const_mul (d i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [covariance_const_mul_left, covariance_const_mul_right, cov_Yc_self s hs]; ring
  · intro k _ hk
    rw [covariance_const_mul_left, covariance_const_mul_right, cov_Yc_ne s j k (Ne.symm hk)]; simp
  · simp


lemma indep_lf (s : ℝ) (hs : 0 ≤ s) {N : ℕ} {κ : Type} [Fintype κ]
    (c : Option (Fin N) → ℝ) (d : κ → Option (Fin N) → ℝ)
    (h : ∀ k, ∑ j, c j * d k j * wt s j = 0) :
    IndepFun (lf c) (fun ω k => lf (d k) ω) (auxMeasure s) := by
  let L : (Option (Fin N) → ℝ) →ₗ[ℝ] (Unit → ℝ) × (κ → ℝ) :=
    { toFun := fun x => (fun _ => ∑ j, c j * x j, fun k => ∑ j, d k j * x j)
      map_add' := by
        intro x y; ext <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        ext <;> simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_mk, RingHom.id_apply] <;>
          rw [Finset.mul_sum] <;> exact Finset.sum_congr rfl (fun j _ => by ring) }
  have hG := (gl_Y s N).map (LinearMap.toContinuousLinearMap L)
  have e : (fun ω => (fun _ : Unit => lf c ω, fun k => lf (d k) ω)) =
      (LinearMap.toContinuousLinearMap L) ∘ (fun (ω : AuxSpace) (j : Option (Fin N)) => Yc j ω) := by
    funext ω
    simp [L, lf]
  have hG' : HasGaussianLaw (fun ω => (fun _ : Unit => lf c ω, fun k => lf (d k) ω)) (auxMeasure s) := by
    rw [e]; exact hG
  have hI := HasGaussianLaw.indepFun_of_covariance_eval (X := fun _ : Unit => lf c)
    (Y := fun k => lf (d k)) hG' (fun _ k => by
      rw [lin_cov s hs]; exact h k)
  exact hI.comp (φ := fun x : Unit → ℝ => x ()) (ψ := id) (measurable_pi_apply ()) measurable_id


noncomputable def cR (l s : ℝ) (n : ℕ) : Option (Fin n) → ℝ
  | none => l / (l + n * s)
  | some _ => -(s * Real.sqrt l) / (l + n * s)

noncomputable def dS (l : ℝ) (n : ℕ) (k : Set.Iic n) : Option (Fin n) → ℝ
  | none => ((k : ℕ) : ℝ)
  | some r => if (r : ℕ) < (k : ℕ) then Real.sqrt l else 0

lemma auxSum_eq (l : ℝ) (n : ℕ) (k : Set.Iic n) (ω : AuxSpace) :
    auxSum l k ω = lf (dS l n k) ω := by
  have hk : (k : ℕ) ≤ n := k.2
  unfold lf auxSum auxSample
  rw [Fintype.sum_option]
  simp only [dS, Yc, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun r => (if r < (k : ℕ) then Real.sqrt l else 0) * ω.2 r) n]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : Finset.filter (fun r => r < (k : ℕ)) (Finset.range n) = Finset.range k := by
    ext r; simp; omega
  rw [this, Finset.mul_sum]


lemma R_eq (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (n : ℕ) (ω : AuxSpace) :
    ω.1 - Zproc l s n ω = lf (cR l s n) ω := by
  have hd : l + n * s ≠ 0 := by positivity
  unfold lf Zproc auxSum auxSample
  rw [Fintype.sum_option]
  simp only [cR, Yc, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun r => ω.2 r) n]
  field_simp
  ring

lemma cov_cR_dS (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (n : ℕ) (k : Set.Iic n) :
    ∑ j, cR l s n j * dS l n k j * wt s j = 0 := by
  have hk : (k : ℕ) ≤ n := k.2
  have hd : l + n * s ≠ 0 := by positivity
  rw [Fintype.sum_option]
  simp only [cR, dS, wt]
  have h1 : ∑ r : Fin n, -(s * Real.sqrt l) / (l + n * s) * (if (r : ℕ) < (k : ℕ) then Real.sqrt l else 0) * 1
      = -(s * Real.sqrt l) / (l + n * s) * (k * Real.sqrt l) := by
    simp_rw [mul_one, ← Finset.mul_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun r => if r < (k : ℕ) then Real.sqrt l else 0) n,
      ← Finset.sum_filter]
    have : Finset.filter (fun r => r < (k : ℕ)) (Finset.range n) = Finset.range k := by
      ext r; simp; omega
    rw [this]; simp [mul_comm]
  rw [h1]
  have h2 : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
  field_simp
  rw [h2]; ring


lemma meas_Yc {N : ℕ} (j : Option (Fin N)) : Measurable (Yc j) := by
  cases j with
  | none => exact measurable_fst
  | some r => exact (measurable_pi_apply _).comp measurable_snd

lemma meas_lf {N : ℕ} (c : Option (Fin N) → ℝ) : Measurable (lf c) := by
  unfold lf
  exact Finset.measurable_sum _ (fun j _ => (meas_Yc j).const_mul _)

lemma integrable_Yc (s : ℝ) {N : ℕ} (j : Option (Fin N)) : Integrable (Yc j) (auxMeasure s) :=
  (memLp_Yc s j).integrable one_le_two

lemma integral_Yc (s : ℝ) {N : ℕ} (j : Option (Fin N)) : ∫ ω, Yc j ω ∂(auxMeasure s) = 0 := by
  cases j with
  | none =>
    have := integral_map (μ := auxMeasure s) (φ := Prod.fst) (f := fun x => x) (by fun_prop)
      (by rw [map_fst_aux]; exact aestronglyMeasurable_id)
    rw [map_fst_aux, integral_id_gaussianReal] at this
    simpa [Yc] using this.symm
  | some r =>
    have := integral_map (μ := auxMeasure s) (φ := Prod.snd) (f := fun w : ℕ → ℝ => w r) (by fun_prop)
      (by rw [map_snd_aux]; exact (measurable_pi_apply _).aestronglyMeasurable)
    rw [map_snd_aux] at this
    have h2 := integral_map (μ := nu) (φ := fun w : ℕ → ℝ => w r) (f := fun x => x)
      (measurable_pi_apply _).aemeasurable
      (by rw [show nu.map (fun w : ℕ → ℝ => w r) = gaussianReal 0 1 from
              Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) r]; exact aestronglyMeasurable_id)
    rw [show nu.map (fun w : ℕ → ℝ => w r) = gaussianReal 0 1 from
              Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) r, integral_id_gaussianReal] at h2
    simp only [Yc]
    rw [← this]; simpa using h2.symm

lemma integrable_lf (s : ℝ) {N : ℕ} (c : Option (Fin N) → ℝ) : Integrable (lf c) (auxMeasure s) := by
  unfold lf
  exact integrable_finsetSum _ (fun j _ => (integrable_Yc s j).const_mul _)

lemma integral_lf (s : ℝ) {N : ℕ} (c : Option (Fin N) → ℝ) : ∫ ω, lf c ω ∂(auxMeasure s) = 0 := by
  unfold lf
  rw [integral_finsetSum _ (fun j _ => (integrable_Yc s j).const_mul _)]
  simp [integral_const_mul, integral_Yc]

lemma auxFiltration_eq (l : ℝ) (n : ℕ) :
    (auxFiltration l n : MeasurableSpace AuxSpace) =
      MeasurableSpace.comap (fun ω (j : Set.Iic n) => auxSum l j ω) inferInstance :=
  Filtration.natural_eq_comap _ _ n

lemma key (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (n : ℕ) :
    Zproc l s n =ᵐ[auxMeasure s] (auxMeasure s)[fun ω : AuxSpace => ω.1 | auxFiltration l n] := by
  have h := indep_lf s hs.le (cR l s n) (dS l n) (cov_cR_dS l s hl hs n)
  have h' : Indep (MeasurableSpace.comap (lf (cR l s n)) inferInstance) (auxFiltration l n)
      (auxMeasure s) := by
    rw [auxFiltration_eq]
    have e : (fun ω (k : Set.Iic n) => lf (dS l n k) ω) = (fun ω (j : Set.Iic n) => auxSum l j ω) := by
      funext ω k; rw [auxSum_eq]
    rw [e] at h
    exact h
  have hce := condExp_indep_eq (μ := auxMeasure s) (f := lf (cR l s n))
    (meas_lf _).comap_le ((auxFiltration l).le n)
    (comap_measurable (lf (cR l s n))).stronglyMeasurable h'
  rw [integral_lf] at hce
  have hxi : Integrable (fun ω : AuxSpace => ω.1) (auxMeasure s) := integrable_Yc s (N := 0) none
  have hZ : Integrable (Zproc l s n) (auxMeasure s) := by
    have := hxi.sub (integrable_lf s (cR l s n))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    rw [← R_eq l s hl hs n ω]; ring
  have hZm : StronglyMeasurable[auxFiltration l n] (Zproc l s n) := by
    have h0 : StronglyMeasurable[auxFiltration l n] (auxSum l n) :=
      Filtration.stronglyAdapted_natural (u := fun τ => auxSum l τ)
        (fun τ => auxSum_stronglyMeasurable l τ) n
    have h1 : StronglyMeasurable[auxFiltration l n] (fun ω => s * auxSum l n ω) := h0.const_mul s
    have h2 : StronglyMeasurable[auxFiltration l n] (fun ω => s * auxSum l n ω / (l + n * s)) :=
      by simpa [div_eq_mul_inv] using StronglyMeasurable.mul_const h1 (l + n * s)⁻¹
    exact h2
  have e : (fun ω : AuxSpace => ω.1) = Zproc l s n + lf (cR l s n) := by
    funext ω
    simp only [Pi.add_apply]
    rw [← R_eq l s hl hs n ω]; ring
  rw [e]
  refine (((condExp_add hZ (integrable_lf s _) _).trans ?_).symm)
  rw [condExp_of_stronglyMeasurable ((auxFiltration l).le n) hZm hZ]
  filter_upwards [hce] with ω hω
  simp [hω]


lemma Zproc_sm (l s : ℝ) (n : ℕ) : StronglyMeasurable[auxFiltration l n] (Zproc l s n) := by
  have h0 : StronglyMeasurable[auxFiltration l n] (auxSum l n) :=
    Filtration.stronglyAdapted_natural (u := fun τ => auxSum l τ)
      (fun τ => auxSum_stronglyMeasurable l τ) n
  have h1 : StronglyMeasurable[auxFiltration l n] (fun ω => s * auxSum l n ω) := h0.const_mul s
  have h2 : StronglyMeasurable[auxFiltration l n] (fun ω => s * auxSum l n ω / (l + n * s)) :=
    by simpa [div_eq_mul_inv] using StronglyMeasurable.mul_const h1 (l + n * s)⁻¹
  exact h2

lemma integrable_xi (s : ℝ) : Integrable (fun ω : AuxSpace => ω.1) (auxMeasure s) :=
  integrable_Yc s (N := 0) none

lemma Zproc_martingale (l s : ℝ) (hl : 0 < l) (hs : 0 < s) :
    Martingale (Zproc l s) (auxFiltration l) (auxMeasure s) := by
  refine ⟨fun n => Zproc_sm l s n, fun i j hij => ?_⟩
  have h1 := condExp_congr_ae (m := auxFiltration l i) (key l s hl hs j)
  have h2 := condExp_condExp_of_le (μ := auxMeasure s) (f := fun ω : AuxSpace => ω.1)
    ((auxFiltration l).mono hij) ((auxFiltration l).le j)
  exact h1.trans (h2.trans (key l s hl hs i).symm)

lemma stopped_eq_condExp (l s : ℝ) (hl : 0 < l) (hs : 0 < s) {T : AuxSpace → WithTop ℕ}
    (hT : IsStoppingTime (auxFiltration l) T) {N : ℕ} (hTN : ∀ ω, T ω ≤ N) :
    stoppedValue (Zproc l s) T =ᵐ[auxMeasure s]
      (auxMeasure s)[fun ω : AuxSpace => ω.1 | hT.measurableSpace] := by
  have h1 := (Zproc_martingale l s hl hs).stoppedValue_ae_eq_condExp_of_le_const hT hTN
  have h2 := condExp_congr_ae (m := hT.measurableSpace) (key l s hl hs N)
  have h3 := condExp_condExp_of_le (μ := auxMeasure s) (f := fun ω : AuxSpace => ω.1)
    (hT.measurableSpace_le_of_le_const hTN) ((auxFiltration l).le N)
  exact h1.trans (h2.trans h3)

lemma Zproc_ui (l s : ℝ) (hl : 0 < l) (hs : 0 < s) :
    UniformIntegrable (Zproc l s) 1 (auxMeasure s) :=
  ((integrable_xi s).uniformIntegrable_condExp_filtration (f := auxFiltration l)).ae_eq
    (fun n => (key l s hl hs n).symm)

end CtCore

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

/-- facts about an admissible lookahead -/
lemma T_facts (l : ℝ) (s : ℝ)
    (T : AuxSpace → WithTop ℕ) (hT : AdmissibleLookahead l T) :
    ∃ N : ℕ, (∀ ω, ∃ m : ℕ, T ω = m ∧ 1 ≤ m ∧ m ≤ N) ∧
      Measurable (fun ω => (((T ω).untopA : ℕ) : ℝ)) ∧
      Integrable (fun ω => (((T ω).untopA : ℕ) : ℝ)) (auxMeasure s) ∧
      (1 : ℝ) ≤ ∫ ω, (((T ω).untopA : ℕ) : ℝ) ∂(auxMeasure s) := by
  obtain ⟨hst, N, hN⟩ := hT
  have hTfin : ∀ ω, ∃ m : ℕ, T ω = m ∧ 1 ≤ m ∧ m ≤ N := by
    intro ω
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1
      (ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hN ω).2)
    refine ⟨m, hm.symm, ?_, ?_⟩
    · have := (hN ω).1
      rw [← hm] at this
      exact WithTop.coe_le_coe.1 this
    · have := (hN ω).2
      rw [← hm] at this
      exact WithTop.coe_le_coe.1 this
  have hTmeas : Measurable (fun ω => (((T ω).untopA : ℕ) : ℝ)) := by
    have h1 : Measurable T := hst.measurable'
    exact (measurable_of_countable (fun x : WithTop ℕ => (((x.untopA : ℕ)) : ℝ))).comp h1
  have hTint : Integrable (fun ω => (((T ω).untopA : ℕ) : ℝ)) (auxMeasure s) := by
    refine Integrable.mono' (g := fun _ => (N : ℝ)) (integrable_const _) hTmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    obtain ⟨m, hm, h1, h2⟩ := hTfin ω
    simp only [hm, WithTop.untopD_coe, Real.norm_eq_abs, Nat.abs_cast]
    exact_mod_cast h2
  refine ⟨N, hTfin, hTmeas, hTint, ?_⟩
  have : ∫ ω, (1 : ℝ) ∂(auxMeasure s) ≤ ∫ ω, (((T ω).untopA : ℕ) : ℝ) ∂(auxMeasure s) := by
    refine integral_mono (integrable_const _) hTint (fun ω => ?_)
    obtain ⟨m, hm, h1, h2⟩ := hTfin ω
    simp only [hm, WithTop.untopD_coe]
    exact_mod_cast h1
  simpa using this

lemma lookahead_le' (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i)
    (T : AuxSpace → WithTop ℕ) (hT : AdmissibleLookahead (lam i) T) :
    lookaheadValue lam c mu Sig i T ≤
      -(∫ ω, (((T ω).untopA : ℕ) : ℝ) ∂(auxMeasure (Sig i i))) +
      Kc Sig i / c i * ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂(auxMeasure (Sig i i)) := by
  obtain ⟨N, hTfin, hTmeas, hTint, -⟩ := T_facts (lam i) (Sig i i) T hT
  obtain ⟨hst, N', hN⟩ := hT
  set P := auxMeasure (Sig i i) with hP
  have hZ := stopped_eq_condExp (lam i) (Sig i i) hl hs hst (N := N') (fun ω => (hN ω).2)
  have hZint : Integrable (stoppedValue (Zproc (lam i) (Sig i i)) T) P :=
    (integrable_condExp).congr hZ.symm
  have hf : Integrable (fun ω => -(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal mu Sig i (stoppedValue (Zproc (lam i) (Sig i i)) T ω)) P :=
    hTint.neg.add ((integrable_terminal mu Sig i hZint).const_mul _)
  have hg : Integrable (fun ω => -(((T ω).untopA : ℕ) : ℝ) + (1 / c i) * (maxMean mu i + Kc Sig i *
      |stoppedValue (Zproc (lam i) (Sig i i)) T ω|)) P :=
    hTint.neg.add (((integrable_const _).add (hZint.abs.const_mul _)).const_mul _)
  have hle : ∀ ω, -(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal mu Sig i (stoppedValue (Zproc (lam i) (Sig i i)) T ω) ≤
      -(((T ω).untopA : ℕ) : ℝ) + (1 / c i) * (maxMean mu i + Kc Sig i *
        |stoppedValue (Zproc (lam i) (Sig i i)) T ω|) := by
    intro ω
    have := terminal_le mu Sig i (stoppedValue (Zproc (lam i) (Sig i i)) T ω)
    have hc' : 0 < 1 / c i := by positivity
    nlinarith
  have hint := integral_mono hf hg hle
  have i1 : ∫ ω, (1 / c i) * (maxMean mu i + Kc Sig i *
      |stoppedValue (Zproc (lam i) (Sig i i)) T ω|) ∂P =
      (1 / c i) * (maxMean mu i + Kc Sig i *
        ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P) := by
    rw [integral_const_mul, integral_add (integrable_const _) (hZint.abs.const_mul _),
      integral_const_mul]
    simp
  have hg_int : ∫ ω, (-(((T ω).untopA : ℕ) : ℝ) + (1 / c i) * (maxMean mu i + Kc Sig i *
      |stoppedValue (Zproc (lam i) (Sig i i)) T ω|)) ∂P =
      -(∫ ω, (((T ω).untopA : ℕ) : ℝ) ∂P) + (1 / c i) * (maxMean mu i + Kc Sig i *
        ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P) := by
    rw [integral_add (f := fun ω => -(((T ω).untopA : ℕ) : ℝ))
      (g := fun ω => (1 / c i) * (maxMean mu i + Kc Sig i *
        |stoppedValue (Zproc (lam i) (Sig i i)) T ω|))
      (hTint.neg : Integrable (fun ω => -(((T ω).untopA : ℕ) : ℝ)) P)
      (((integrable_const _).add (hZint.abs.const_mul _)).const_mul _), i1, integral_neg]
  unfold lookaheadValue
  rw [hg_int] at hint
  have e : 1 / c i * (maxMean mu i + Kc Sig i *
        ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P) - 1 / c i * maxMean mu i =
      Kc Sig i / c i * ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P := by ring
  linarith

lemma lookahead_le (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i)
    (T : AuxSpace → WithTop ℕ) (hT : AdmissibleLookahead (lam i) T) :
    lookaheadValue lam c mu Sig i T ≤
      -1 + Kc Sig i / c i * ∫ ω, |ω.1| ∂(auxMeasure (Sig i i)) := by
  have h1 := lookahead_le' lam c mu Sig i hl hs hc T hT
  obtain ⟨N, hTfin, hTmeas, hTint, hT1⟩ := T_facts (lam i) (Sig i i) T hT
  obtain ⟨hst, N', hN⟩ := hT
  set P := auxMeasure (Sig i i) with hP
  have hZ := stopped_eq_condExp (lam i) (Sig i i) hl hs hst (N := N') (fun ω => (hN ω).2)
  have habs : ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P ≤ ∫ ω, |ω.1| ∂P := by
    calc ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P
        = ∫ ω, |P[fun ω : AuxSpace => ω.1 | hst.measurableSpace] ω| ∂P :=
          integral_congr_ae (hZ.mono fun ω h => by dsimp only; rw [h])
      _ ≤ ∫ ω, |ω.1| ∂P := integral_abs_condExp_le _
  have hK := Kc_nonneg Sig i
  have : Kc Sig i / c i * ∫ ω, |ω.1| ∂P ≥
      Kc Sig i / c i * ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  linarith

lemma adm_one (l : ℝ) : AdmissibleLookahead l (fun _ => (1 : WithTop ℕ)) :=
  ⟨isStoppingTime_const _ 1, 1, fun _ => ⟨le_rfl, le_rfl⟩⟩

lemma lookahead_one (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i) :
    lookaheadValue lam c mu Sig i (fun _ => (1 : WithTop ℕ)) = nuCKG1 lam c mu Sig i := by
  have hZint : Integrable (Zproc (lam i) (Sig i i) 1) (auxMeasure (Sig i i)) :=
    (Zproc_martingale _ _ hl hs).integrable 1
  have hti := integrable_terminal mu Sig i hZint
  unfold lookaheadValue nuCKG1
  have e : (fun ω => (-((((fun _ : AuxSpace => (1 : WithTop ℕ)) ω).untopA : ℕ) : ℝ)
      + (1 / c i) * terminal mu Sig i (stoppedValue (Zproc (lam i) (Sig i i))
        (fun _ => (1 : WithTop ℕ)) ω))) =
      fun ω => -1 + (1 / c i) * terminal mu Sig i (Zproc (lam i) (Sig i i) 1 ω) := by
    funext ω
    have : ((1 : WithTop ℕ).untopA : ℕ) = 1 := rfl
    simp [stoppedValue, this]
  rw [e, integral_add (integrable_const _) (hti.const_mul _), integral_const_mul]
  simp

theorem ec1 (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i) :
    nuCKG1 lam c mu Sig i ≤ nuStar lam c mu Sig i := by
  unfold nuStar
  refine le_csSup ⟨-1 + Kc Sig i / c i * ∫ ω, |ω.1| ∂(auxMeasure (Sig i i)), ?_⟩
    ⟨fun _ => (1 : WithTop ℕ), adm_one _, (lookahead_one lam c mu Sig i hl hs hc).symm⟩
  rintro v ⟨T, hT, rfl⟩
  exact lookahead_le lam c mu Sig i hl hs hc T hT

end main

end CtCore

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


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace PmA
open CtCore

variable {M : ℕ}

lemma terminal_sub_le (mu mu' : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ) (i : Fin M) (D : ℝ)
    (hD : ∀ j, |mu j - mu' j| ≤ D) (z : ℝ) :
    terminal mu S i z ≤ terminal mu' S i z + D := by
  unfold terminal
  refine Finset.sup'_le _ _ (fun j _ => ?_)
  have h1 : mu' j + S i j / S i i * z ≤
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (fun j => mu' j + S i j / S i i * z) :=
    Finset.le_sup' (fun j => mu' j + S i j / S i i * z) (Finset.mem_univ j)
  have := (abs_le.1 (hD j)).2
  linarith

lemma maxMean_sub_le (mu mu' : Fin M → ℝ) (i : Fin M) (D : ℝ)
    (hD : ∀ j, |mu j - mu' j| ≤ D) : maxMean mu i ≤ maxMean mu' i + D := by
  unfold maxMean
  refine Finset.sup'_le _ _ (fun j _ => ?_)
  have h1 : mu' j ≤ Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ mu' :=
    Finset.le_sup' mu' (Finset.mem_univ j)
  have := (abs_le.1 (hD j)).2
  linarith

lemma lookahead_sub_le (lam c : Fin M → ℝ) (mu mu' : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ)
    (i : Fin M) (hl : 0 < lam i) (hs : 0 < S i i) (hc : 0 < c i)
    (T : AuxSpace → WithTop ℕ) (hT : AdmissibleLookahead (lam i) T) (D : ℝ)
    (hD : ∀ j, |mu j - mu' j| ≤ D) :
    lookaheadValue lam c mu S i T ≤ lookaheadValue lam c mu' S i T + 2 * D / c i := by
  obtain ⟨N, hTfin, hTmeas, hTint, -⟩ := T_facts (lam i) (S i i) T hT
  obtain ⟨hst, N', hN⟩ := hT
  set P := auxMeasure (S i i) with hP
  have hZ := stopped_eq_condExp (lam i) (S i i) hl hs hst (N := N') (fun ω => (hN ω).2)
  have hZint : Integrable (stoppedValue (Zproc (lam i) (S i i)) T) P :=
    (integrable_condExp).congr hZ.symm
  have hf : ∀ m : Fin M → ℝ, Integrable (fun ω => -(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal m S i (stoppedValue (Zproc (lam i) (S i i)) T ω)) P :=
    fun m => hTint.neg.add ((integrable_terminal m S i hZint).const_mul _)
  have hD' : ∀ j, |mu' j - mu j| ≤ D := fun j => by rw [abs_sub_comm]; exact hD j
  have hle : ∀ ω, -(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal mu S i (stoppedValue (Zproc (lam i) (S i i)) T ω) ≤
      (-(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal mu' S i (stoppedValue (Zproc (lam i) (S i i)) T ω)) + D / c i := by
    intro ω
    have := terminal_sub_le mu mu' S i D hD (stoppedValue (Zproc (lam i) (S i i)) T ω)
    have hc' : 0 < 1 / c i := by positivity
    have : 1 / c i * terminal mu S i (stoppedValue (Zproc (lam i) (S i i)) T ω) ≤
        1 / c i * (terminal mu' S i (stoppedValue (Zproc (lam i) (S i i)) T ω) + D) :=
      mul_le_mul_of_nonneg_left this hc'.le
    have e : 1 / c i * (terminal mu' S i (stoppedValue (Zproc (lam i) (S i i)) T ω) + D) =
        1 / c i * terminal mu' S i (stoppedValue (Zproc (lam i) (S i i)) T ω) + D / c i := by ring
    linarith
  have hf2 : Integrable (fun ω => (-(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal mu' S i (stoppedValue (Zproc (lam i) (S i i)) T ω)) + D / c i) P :=
    (hf mu').add (integrable_const (D / c i))
  have hint := integral_mono (hf mu) hf2 hle
  rw [integral_add (hf mu') (integrable_const _)] at hint
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul] at hint
  have hm := maxMean_sub_le mu' mu i D hD'
  unfold lookaheadValue
  have hc' : 0 < 1 / c i := by positivity
  have : 1 / c i * maxMean mu' i ≤ 1 / c i * (maxMean mu i + D) :=
    mul_le_mul_of_nonneg_left hm hc'.le
  have e : 2 * D / c i = D / c i + 1 / c i * D := by ring
  rw [e]
  nlinarith

lemma nuStar_sub_le (lam c : Fin M → ℝ) (mu mu' : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ)
    (i : Fin M) (hl : 0 < lam i) (hs : 0 < S i i) (hc : 0 < c i) (D : ℝ)
    (hD : ∀ j, |mu j - mu' j| ≤ D) :
    nuStar lam c mu S i ≤ nuStar lam c mu' S i + 2 * D / c i := by
  have hbdd : ∀ m : Fin M → ℝ, BddAbove {v | ∃ T, AdmissibleLookahead (lam i) T ∧
      v = lookaheadValue lam c m S i T} := fun m =>
    ⟨-1 + Kc S i / c i * ∫ ω, |ω.1| ∂(auxMeasure (S i i)), by
      rintro v ⟨T, hT, rfl⟩; exact lookahead_le lam c m S i hl hs hc T hT⟩
  unfold nuStar
  refine csSup_le ⟨_, ⟨fun _ => (1 : WithTop ℕ), adm_one _, rfl⟩⟩ ?_
  rintro v ⟨T, hT, rfl⟩
  have h1 := lookahead_sub_le lam c mu mu' S i hl hs hc T hT D hD
  have h2 : lookaheadValue lam c mu' S i T ≤ sSup {v | ∃ T, AdmissibleLookahead (lam i) T ∧
      v = lookaheadValue lam c mu' S i T} := le_csSup (hbdd mu') ⟨T, hT, rfl⟩
  linarith

lemma continuous_nuStar (lam c : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ)
    (i : Fin M) (hl : 0 < lam i) (hs : 0 < S i i) (hc : 0 < c i) :
    Continuous (fun mu => nuStar lam c mu S i) := by
  have hL : LipschitzWith (Real.toNNReal (2 / c i)) (fun mu => nuStar lam c mu S i) := by
    refine LipschitzWith.of_dist_le_mul fun mu mu' => ?_
    have hD : ∀ j, |mu j - mu' j| ≤ dist mu mu' := fun j => by
      rw [← Real.dist_eq]; exact dist_le_pi_dist mu mu' j
    have hD' : ∀ j, |mu' j - mu j| ≤ dist mu mu' := fun j => by
      rw [abs_sub_comm]; exact hD j
    have h1 := nuStar_sub_le lam c mu mu' S i hl hs hc _ hD
    have h2 := nuStar_sub_le lam c mu' mu S i hl hs hc _ hD'
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), abs_le]
    have e : 2 * dist mu mu' / c i = 2 / c i * dist mu mu' := by ring
    constructor <;> linarith
  exact hL.continuous

/-- Characterization of the least-index argmax. -/
lemma leastArgmax_eq_iff (hM : 0 < M) (g : Fin M → ℝ) (a : Fin M) :
    leastArgmax hM g = a ↔ (∀ j, g j ≤ g a) ∧ ∀ b, b < a → ∃ j, g b < g j := by
  set s := Finset.univ.filter fun i => ∀ j, g j ≤ g i with hs
  have hne : s.Nonempty := by
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ g
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM⟩⟩)
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hk j (Finset.mem_univ _)⟩⟩
  have hdef : leastArgmax hM g = s.min' hne := rfl
  rw [hdef]
  constructor
  · rintro rfl
    refine ⟨(Finset.mem_filter.1 (Finset.min'_mem s hne)).2, fun b hb => ?_⟩
    by_contra hc
    push_neg at hc
    have hbs : b ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩
    exact absurd (Finset.min'_le s b hbs) (not_le.2 hb)
  · rintro ⟨h1, h2⟩
    have has : a ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    refine le_antisymm (Finset.min'_le s a has) ?_
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := h2 _ hlt
    have := (Finset.mem_filter.1 (Finset.min'_mem s hne)).2 j
    linarith

lemma measurable_leastArgmax {X : Type*} [MeasurableSpace X] (hM : 0 < M) (g : X → Fin M → ℝ)
    (hg : ∀ j, Measurable fun x => g x j) : Measurable fun x => leastArgmax hM (g x) := by
  refine measurable_to_countable' fun a => ?_
  have : (fun x => leastArgmax hM (g x)) ⁻¹' {a} =
      (⋂ j, {x | g x j ≤ g x a}) ∩ ⋂ b, ⋂ (_ : b < a), ⋃ j, {x | g x b < g x j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, leastArgmax_eq_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => measurableSet_le (hg j) (hg a)) ?_
  exact MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
    MeasurableSet.iUnion fun j => measurableSet_lt (hg b) (hg j)

/-- For a fixed covariance with positive diagonal, the cPDE choice is a measurable function of
the posterior mean. -/
lemma measurable_cpdeChoice (I : Instance M) (S : Matrix (Fin M) (Fin M) ℝ)
    (hS : ∀ i, 0 < S i i) (n : Fin M → ℕ) {X : Type*} [MeasurableSpace X] (f : X → Fin M → ℝ)
    (hf : Measurable f) : Measurable fun x => cpdeChoice I (f x, S, n) := by
  unfold cpdeChoice
  refine measurable_leastArgmax _ _ fun j => ?_
  exact (continuous_nuStar I.lam I.c S j (I.lam_pos j) (hS j) (I.c_pos j)).measurable.comp hf

end PmA


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace PmB

variable {M : ℕ} (I : Instance M)

/-- One step of the cPDE recursion fed with an observation `y`. -/
noncomputable def step (s : State M) (y : ℝ) : State M :=
  ((update I.lam s.1 s.2.1 (cpdeChoice I s) y).1, (update I.lam s.1 s.2.1 (cpdeChoice I s) y).2,
    Function.update s.2.2 (cpdeChoice I s) (s.2.2 (cpdeChoice I s) + 1))

/-- Replay of the cPDE recursion on a deterministic observation sequence. -/
noncomputable def rep : ℕ → (ℕ → ℝ) → State M
  | 0, _ => (I.mu0, I.Sig0, fun _ => 0)
  | t + 1, y => step I (rep t y) (y t)

/-- The observation sequence of the trial. -/
noncomputable def obsN (ω : TrialSpace M) (s : ℕ) : ℝ :=
  W I (alloc I s ω) (count I s ω (alloc I s ω)) ω

lemma cpdeState_eq_rep (t : ℕ) (ω : TrialSpace M) : cpdeState I t ω = rep I t (obsN I ω) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show cpdeState I (t + 1) ω = step I (rep I t (obsN I ω)) (obsN I ω t)
    rw [← ih]; rfl

lemma rep_congr (t : ℕ) (y y' : ℕ → ℝ) (h : ∀ s < t, y s = y' s) : rep I t y = rep I t y' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show step I (rep I t y) (y t) = step I (rep I t y') (y' t)
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

/-! Fixed allocation sequences. -/

noncomputable def kal (α : ℕ → Fin M) : ℕ → (ℕ → ℝ) → (Fin M → ℝ) × Matrix (Fin M) (Fin M) ℝ
  | 0, _ => (I.mu0, I.Sig0)
  | t + 1, y => update I.lam (kal α t y).1 (kal α t y).2 (α t) (y t)

def cnt (α : ℕ → Fin M) : ℕ → Fin M → ℕ
  | 0 => fun _ => 0
  | t + 1 => Function.update (cnt α t) (α t) (cnt α t (α t) + 1)

noncomputable def SigA (α : ℕ → Fin M) (t : ℕ) : Matrix (Fin M) (Fin M) ℝ := (kal I α t 0).2

lemma kal_snd (α : ℕ → Fin M) (t : ℕ) (y : ℕ → ℝ) : (kal I α t y).2 = SigA I α t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [SigA, kal, update] at ih ⊢
    rw [ih, ← SigA]

lemma SigA_succ (α : ℕ → Fin M) (t : ℕ) :
    SigA I α (t + 1) = CtMat.Step I.lam (SigA I α t) (α t) := by
  show (kal I α (t + 1) 0).2 = _
  simp only [kal, update, CtMat.Step]
  rw [kal_snd]

lemma SigA_posDef (α : ℕ → Fin M) (t : ℕ) : (SigA I α t).PosDef := by
  induction t with
  | zero => exact I.posDef
  | succ t ih => rw [SigA_succ]; exact CtMat.step_posDef ih _ _ (I.lam_pos _)

lemma kal_succ_fst (α : ℕ → Fin M) (t : ℕ) (y : ℕ → ℝ) (j : Fin M) :
    (kal I α (t + 1) y).1 j = (kal I α t y).1 j + (y t - (kal I α t y).1 (α t)) /
      (I.lam (α t) + SigA I α t (α t) (α t)) * SigA I α t j (α t) := by
  simp only [kal, update]; rw [kal_snd]

lemma kal_congr (α : ℕ → Fin M) (t : ℕ) (y y' : ℕ → ℝ) (h : ∀ s < t, y s = y' s) :
    kal I α t y = kal I α t y' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show update I.lam (kal I α t y).1 (kal I α t y).2 (α t) (y t) =
      update I.lam (kal I α t y').1 (kal I α t y').2 (α t) (y' t)
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

lemma kal_congr_alloc (α α' : ℕ → Fin M) (t : ℕ) (y : ℕ → ℝ) (h : ∀ s < t, α s = α' s) :
    kal I α t y = kal I α' t y := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show update I.lam (kal I α t y).1 (kal I α t y).2 (α t) (y t) =
      update I.lam (kal I α' t y).1 (kal I α' t y).2 (α' t) (y t)
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

lemma cnt_congr_alloc (α α' : ℕ → Fin M) (t : ℕ) (h : ∀ s < t, α s = α' s) :
    cnt α t = cnt α' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show Function.update (cnt α t) (α t) (cnt α t (α t) + 1) =
      Function.update (cnt α' t) (α' t) (cnt α' t (α' t) + 1)
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

lemma SigA_congr_alloc (α α' : ℕ → Fin M) (t : ℕ) (h : ∀ s < t, α s = α' s) :
    SigA I α t = SigA I α' t := by
  unfold SigA; rw [kal_congr_alloc I α α' t 0 h]

lemma measurable_kal (α : ℕ → Fin M) (t : ℕ) : Measurable fun y => (kal I α t y).1 := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    rw [measurable_pi_iff]
    intro j
    simp_rw [kal_succ_fst]
    have h1 : Measurable fun y => (kal I α t y).1 j := (measurable_pi_apply j).comp ih
    have h2 : Measurable fun y => (kal I α t y).1 (α t) := (measurable_pi_apply _).comp ih
    have h3 : Measurable fun y : ℕ → ℝ => y t := measurable_pi_apply t
    exact h1.add (((h3.sub h2).div_const _).mul_const _)

/-! The events on which the replayed allocation follows a given sequence. -/

def Dset (α : ℕ → Fin M) (t : ℕ) : Set (ℕ → ℝ) := {y | ∀ s < t, cpdeChoice I (rep I s y) = α s}

lemma rep_eq_of_mem (α : ℕ → Fin M) (t : ℕ) (y : ℕ → ℝ) (h : y ∈ Dset I α t) :
    rep I t y = ((kal I α t y).1, SigA I α t, cnt α t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => h s (by omega))
    have hc : cpdeChoice I (rep I t y) = α t := h t (by omega)
    show step I (rep I t y) (y t) = _
    unfold step
    rw [hc, ih', SigA_succ]
    simp only [kal, cnt, update, kal_snd, CtMat.Step]

lemma Dset_succ (α : ℕ → Fin M) (t : ℕ) :
    Dset I α (t + 1) = Dset I α t ∩
      {y | cpdeChoice I ((kal I α t y).1, SigA I α t, cnt α t) = α t} := by
  ext y
  constructor
  · intro h
    have hD : y ∈ Dset I α t := fun s hs => h s (by omega)
    refine ⟨hD, ?_⟩
    have := h t (by omega)
    rw [rep_eq_of_mem I α t y hD] at this
    exact this
  · rintro ⟨hD, h2⟩ s hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | hs
    · exact hD s hs
    · subst hs
      rw [rep_eq_of_mem I α s y hD]; exact h2

lemma measurableSet_Dset (α : ℕ → Fin M) (t : ℕ) : MeasurableSet (Dset I α t) := by
  induction t with
  | zero =>
    have : Dset I α 0 = Set.univ := by ext y; simp [Dset]
    rw [this]; exact MeasurableSet.univ
  | succ t ih =>
    rw [Dset_succ]
    refine ih.inter ?_
    have hm := PmA.measurable_cpdeChoice I (SigA I α t) (fun i => (SigA_posDef I α t).diag_pos)
      (cnt α t) (fun y => (kal I α t y).1) (measurable_kal I α t)
    exact hm (measurableSet_singleton (α t))

/-- The allocation sequence of a replay. -/
noncomputable def allocSeq (y : ℕ → ℝ) : ℕ → Fin M := fun s => cpdeChoice I (rep I s y)

lemma mem_Dset_allocSeq (y : ℕ → ℝ) (t : ℕ) : y ∈ Dset I (allocSeq I y) t := fun _ _ => rfl

/-- Extension of a finite allocation history. -/
def extA (hM : 0 < M) {t : ℕ} (a : Fin t → Fin M) : ℕ → Fin M :=
  fun s => if h : s < t then a ⟨s, h⟩ else ⟨0, hM⟩

lemma extA_restrict (hM : 0 < M) (t : ℕ) (α : ℕ → Fin M) :
    ∀ s < t, extA hM (fun r : Fin t => α r) s = α s := by
  intro s hs; simp [extA, hs]

lemma Dset_congr_alloc (α α' : ℕ → Fin M) (t : ℕ) (h : ∀ s < t, α s = α' s) :
    Dset I α t = Dset I α' t := by
  ext y; constructor
  · intro hy s hs; rw [← h s hs]; exact hy s hs
  · intro hy s hs; rw [h s hs]; exact hy s hs

/-- A function agreeing with measurable functions on the pieces of a finite measurable cover is
measurable. -/
lemma measurable_of_cover {X β A : Type*} [MeasurableSpace X] [MeasurableSpace β] [Finite A]
    (D : A → Set X) (hD : ∀ a, MeasurableSet (D a)) (hcov : ∀ x, ∃ a, x ∈ D a)
    (f : X → β) (g : A → X → β) (hg : ∀ a, Measurable (g a)) (hfg : ∀ a x, x ∈ D a → f x = g a x) :
    Measurable f := by
  intro B hB
  have : f ⁻¹' B = ⋃ a, D a ∩ g a ⁻¹' B := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hcov x
      exact ⟨a, ha, by rw [← hfg a x ha]; exact hx⟩
    · rintro ⟨a, ha, hx⟩
      rw [hfg a x ha]; exact hx
  rw [this]
  exact MeasurableSet.iUnion fun a => (hD a).inter (hg a hB)

lemma hM0 {M : ℕ} (I : Instance M) : 0 < M := by have := I.two_le; omega

/-- Cover of the observation space by the finitely many allocation histories up to `t`. -/
lemma cover (t : ℕ) (y : ℕ → ℝ) :
    ∃ a : Fin t → Fin M, y ∈ Dset I (extA (hM0 I) a) t := by
  refine ⟨fun r => allocSeq I y r, ?_⟩
  rw [Dset_congr_alloc I _ (allocSeq I y) t (extA_restrict (hM0 I) t _)]
  exact mem_Dset_allocSeq I y t

lemma rep_eq_of_mem' (t : ℕ) (a : Fin t → Fin M) (y : ℕ → ℝ)
    (h : y ∈ Dset I (extA (hM0 I) a) t) :
    rep I t y = ((kal I (extA (hM0 I) a) t y).1, SigA I (extA (hM0 I) a) t,
      cnt (extA (hM0 I) a) t) := rep_eq_of_mem I _ t y h

lemma measurable_rep_fst (t : ℕ) : Measurable fun y => (rep I t y).1 :=
  measurable_of_cover (fun a : Fin t → Fin M => Dset I (extA (hM0 I) a) t)
    (fun a => measurableSet_Dset I _ t) (cover I t) _ (fun a y => (kal I (extA (hM0 I) a) t y).1)
    (fun a => measurable_kal I _ t) (fun a y h => by rw [rep_eq_of_mem' I t a y h])

lemma measurable_rep_sig (t : ℕ) (i j : Fin M) : Measurable fun y => (rep I t y).2.1 i j :=
  measurable_of_cover (fun a : Fin t → Fin M => Dset I (extA (hM0 I) a) t)
    (fun a => measurableSet_Dset I _ t) (cover I t) _ (fun a _ => SigA I (extA (hM0 I) a) t i j)
    (fun a => measurable_const) (fun a y h => by rw [rep_eq_of_mem' I t a y h])

lemma measurable_rep_cnt (t : ℕ) : Measurable fun y => (rep I t y).2.2 :=
  measurable_of_cover (fun a : Fin t → Fin M => Dset I (extA (hM0 I) a) t)
    (fun a => measurableSet_Dset I _ t) (cover I t) _ (fun a _ => cnt (extA (hM0 I) a) t)
    (fun a => measurable_const) (fun a y h => by rw [rep_eq_of_mem' I t a y h])

lemma measurable_rep_choice (t : ℕ) : Measurable fun y => cpdeChoice I (rep I t y) :=
  measurable_of_cover (fun a : Fin t → Fin M => Dset I (extA (hM0 I) a) t)
    (fun a => measurableSet_Dset I _ t) (cover I t) _
    (fun a y => cpdeChoice I ((kal I (extA (hM0 I) a) t y).1, SigA I (extA (hM0 I) a) t,
      cnt (extA (hM0 I) a) t))
    (fun a => PmA.measurable_cpdeChoice I _ (fun i => (SigA_posDef I _ t).diag_pos) _ _
      (measurable_kal I _ t))
    (fun a y h => by rw [rep_eq_of_mem' I t a y h])

/-! Measurability of the observation sequence. -/

def trunc (t : ℕ) (y : ℕ → ℝ) : ℕ → ℝ := fun r => if r < t then y r else 0

lemma rep_trunc (t : ℕ) (y : ℕ → ℝ) : rep I t y = rep I t (trunc t y) :=
  rep_congr I t _ _ (fun s hs => by simp [trunc, hs])

lemma measurable_W_eval {X : Type*} [MeasurableSpace X] (a : X → Fin M) (k : X → ℕ)
    (f : X → TrialSpace M) (ha : Measurable a) (hk : Measurable k) (hf : Measurable f) :
    Measurable fun x => W I (a x) (k x) (f x) := by
  have hW : Measurable fun p : (Fin M × ℕ) × TrialSpace M => W I p.1.1 p.1.2 p.2 := by
    refine measurable_from_prod_countable_right fun q => ?_
    show Measurable fun ω => W I q.1 q.2 ω
    unfold W theta
    fun_prop
  exact hW.comp ((ha.prodMk hk).prodMk hf)

lemma measurable_obsN (s : ℕ) : Measurable fun ω => obsN I ω s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have htr : Measurable fun ω => trunc s (obsN I ω) := by
      rw [measurable_pi_iff]
      intro r
      by_cases hr : r < s
      · simpa [trunc, hr] using ih r hr
      · simp only [trunc, hr, if_false]; exact measurable_const
    have halloc : (fun ω => alloc I s ω) = fun ω => cpdeChoice I (rep I s (trunc s (obsN I ω))) := by
      funext ω; rw [← rep_trunc, ← cpdeState_eq_rep]; rfl
    have hcount : (fun ω => count I s ω) = fun ω => (rep I s (trunc s (obsN I ω))).2.2 := by
      funext ω; rw [← rep_trunc, ← cpdeState_eq_rep]; rfl
    have ha : Measurable fun ω => alloc I s ω := by
      rw [halloc]; exact (measurable_rep_choice I s).comp htr
    have hc : Measurable fun ω => count I s ω := by
      rw [hcount]; exact (measurable_rep_cnt I s).comp htr
    have hk : Measurable fun ω => count I s ω (alloc I s ω) := by
      have : Measurable fun p : (Fin M → ℕ) × Fin M => p.1 p.2 :=
        measurable_from_prod_countable_left fun b => measurable_pi_apply b
      exact this.comp (hc.prodMk ha)
    exact measurable_W_eval I _ _ _ ha hk measurable_id

/-- Extension of a finite observation vector. -/
def extY (t : ℕ) (z : Fin t → ℝ) : ℕ → ℝ := fun r => if h : r < t then z ⟨r, h⟩ else 0

lemma measurable_extY (t : ℕ) : Measurable (extY t) := by
  rw [measurable_pi_iff]; intro r
  by_cases h : r < t
  · simp only [extY, h, dif_pos]; exact measurable_pi_apply _
  · simp only [extY, h, dif_neg, not_false_eq_true]; exact measurable_const

lemma cpdeState_eq_ext (t : ℕ) (ω : TrialSpace M) :
    cpdeState I t ω = rep I t (extY t (fun s : Fin t => obsN I ω s)) := by
  rw [cpdeState_eq_rep]
  exact rep_congr I t _ _ (fun s hs => by simp [extY, hs])

end PmB


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace PmC
open PmB

variable {M : ℕ} (I : Instance M)

/-! ### The events `{u_s = α_s, s < t}` -/

noncomputable def Zα (α : ℕ → Fin M) (ω : TrialSpace M) : ℕ → ℝ :=
  fun s => W I (α s) (cnt α s (α s)) ω

def Hset (α : ℕ → Fin M) (t : ℕ) : Set (TrialSpace M) := {ω | ∀ s < t, alloc I s ω = α s}

lemma alloc_eq_rep (s : ℕ) (ω : TrialSpace M) :
    alloc I s ω = cpdeChoice I (rep I s (obsN I ω)) := by
  unfold alloc; rw [cpdeState_eq_rep]

lemma count_eq_rep (s : ℕ) (ω : TrialSpace M) : count I s ω = (rep I s (obsN I ω)).2.2 := by
  unfold count; rw [cpdeState_eq_rep]

lemma mem_Hset_iff (α : ℕ → Fin M) (t : ℕ) (ω : TrialSpace M) :
    ω ∈ Hset I α t ↔ obsN I ω ∈ Dset I α t := by
  simp only [Hset, Dset, Set.mem_setOf_eq, alloc_eq_rep]

lemma obsN_eq_Z (α : ℕ → Fin M) (t : ℕ) (ω : TrialSpace M) (h : ω ∈ Hset I α t) :
    ∀ s < t, obsN I ω s = Zα I α ω s := by
  intro s hs
  have hD : obsN I ω ∈ Dset I α s := (mem_Hset_iff I α s ω).1 (fun r hr => h r (by omega))
  have hrep := rep_eq_of_mem I α s _ hD
  have hc : count I s ω = cnt α s := by rw [count_eq_rep, hrep]
  unfold obsN Zα
  rw [h s hs, hc]

lemma Dset_congr (α : ℕ → Fin M) (t : ℕ) (y y' : ℕ → ℝ) (h : ∀ s < t, y s = y' s) :
    y ∈ Dset I α t ↔ y' ∈ Dset I α t := by
  simp only [Dset, Set.mem_setOf_eq]
  constructor
  · intro hy s hs; rw [← rep_congr I s y y' (fun r hr => h r (by omega))]; exact hy s hs
  · intro hy s hs; rw [rep_congr I s y y' (fun r hr => h r (by omega))]; exact hy s hs

lemma Hset_eq (α : ℕ → Fin M) (t : ℕ) : Hset I α t = Zα I α ⁻¹' Dset I α t := by
  induction t with
  | zero => ext ω; simp [Hset, Dset]
  | succ t ih =>
    ext ω
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have hH : ω ∈ Hset I α t := fun s hs => h s (by omega)
      have hD : Zα I α ω ∈ Dset I α t := by rw [ih] at hH; exact hH
      intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | hs
      · exact hD s hs
      · subst hs
        rw [← rep_congr I s _ _ (obsN_eq_Z I α s ω hH), ← alloc_eq_rep]
        exact h s (by omega)
    · intro h
      have hD : Zα I α ω ∈ Dset I α t := fun s hs => h s (by omega)
      have hH : ω ∈ Hset I α t := by rw [ih]; exact hD
      intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | hs
      · exact hH s hs
      · subst hs
        rw [alloc_eq_rep, rep_congr I s _ _ (obsN_eq_Z I α s ω hH)]
        exact h s (by omega)

lemma mu_eq_on_H (α : ℕ → Fin M) (T : ℕ) (ω : TrialSpace M) (h : ω ∈ Hset I α T) :
    mu I T ω = (kal I α T (Zα I α ω)).1 ∧ Sig I T ω = SigA I α T := by
  have hD := (mem_Hset_iff I α T ω).1 h
  have hrep := rep_eq_of_mem I α T _ hD
  unfold mu Sig
  rw [cpdeState_eq_rep, hrep]
  exact ⟨by rw [kal_congr I α T _ _ (obsN_eq_Z I α T ω h)], rfl⟩

lemma measurable_Zα (α : ℕ → Fin M) (s : ℕ) : Measurable fun ω => Zα I α ω s :=
  measurable_W_eval I (fun _ => α s) (fun _ => cnt α s (α s)) id measurable_const
    measurable_const measurable_id

/-! ### Base distributional facts -/

instance : IsProbabilityMeasure (trialMeasure I) := by unfold trialMeasure; infer_instance

lemma map_fst_trial : (trialMeasure I).map Prod.fst =
    multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0 := by
  unfold trialMeasure; rw [Measure.map_fst_prod]; simp

lemma map_snd_trial : (trialMeasure I).map Prod.snd =
    Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1 := by
  unfold trialMeasure; rw [Measure.map_snd_prod]; simp

lemma map_eps (p : Fin M × ℕ) :
    (trialMeasure I).map (fun ω : TrialSpace M => ω.2 p) = gaussianReal 0 1 := by
  have : (fun ω : TrialSpace M => ω.2 p) = (fun w : Fin M × ℕ → ℝ => w p) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (by fun_prop) measurable_snd, map_snd_trial]
  exact Measure.infinitePi_map_eval _ p

lemma map_theta (j : Fin M) :
    (trialMeasure I).map (fun ω : TrialSpace M => theta ω j) =
      gaussianReal (I.mu0 j) (I.Sig0 j j).toNNReal := by
  have : (fun ω : TrialSpace M => theta ω j) = (fun x : EuclideanSpace ℝ (Fin M) => x j) ∘ Prod.fst :=
    rfl
  rw [this, ← Measure.map_map (by fun_prop) measurable_fst, map_fst_trial]
  exact (measurePreserving_eval_multivariateGaussian I.posDef.posSemidef).map_eq

lemma memLp_eps (p : Fin M × ℕ) : MemLp (fun ω : TrialSpace M => ω.2 p) 2 (trialMeasure I) := by
  have h : MemLp (fun x : ℝ => x) 2 ((trialMeasure I).map (fun ω : TrialSpace M => ω.2 p)) := by
    rw [map_eps]; exact memLp_id_gaussianReal 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).1 h

lemma memLp_theta (j : Fin M) : MemLp (fun ω : TrialSpace M => theta ω j) 2 (trialMeasure I) := by
  have h : MemLp (fun x : ℝ => x) 2 ((trialMeasure I).map (fun ω : TrialSpace M => theta ω j)) := by
    rw [map_theta]; exact memLp_id_gaussianReal 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).1 h

lemma integral_eps (p : Fin M × ℕ) : ∫ ω, ω.2 p ∂(trialMeasure I) = 0 := by
  have := integral_map (μ := trialMeasure I) (φ := fun ω : TrialSpace M => ω.2 p)
    (f := fun x => x) (by fun_prop) (by rw [map_eps]; exact aestronglyMeasurable_id)
  rw [map_eps, integral_id_gaussianReal] at this
  exact this.symm

lemma integral_theta (j : Fin M) : ∫ ω, theta ω j ∂(trialMeasure I) = I.mu0 j := by
  have := integral_map (μ := trialMeasure I) (φ := fun ω : TrialSpace M => theta ω j)
    (f := fun x => x) (by unfold theta; fun_prop) (by rw [map_theta]; exact aestronglyMeasurable_id)
  rw [map_theta, integral_id_gaussianReal] at this
  exact this.symm

lemma cov_theta_theta (j k : Fin M) :
    cov[fun ω => theta ω j, fun ω => theta ω k; trialMeasure I] = I.Sig0 j k := by
  have e := covariance_map (μ := trialMeasure I) (Z := Prod.fst)
    (X := fun x : EuclideanSpace ℝ (Fin M) => x j) (Y := fun x : EuclideanSpace ℝ (Fin M) => x k)
    (by fun_prop) (by fun_prop) (by fun_prop)
  rw [map_fst_trial, covariance_eval_multivariateGaussian I.posDef.posSemidef] at e
  exact e.symm

lemma var_eps (p : Fin M × ℕ) :
    cov[fun ω : TrialSpace M => ω.2 p, fun ω => ω.2 p; trialMeasure I] = 1 := by
  rw [covariance_self (by fun_prop)]
  have := variance_map (μ := trialMeasure I) (X := id) (Y := fun ω : TrialSpace M => ω.2 p)
    (by rw [map_eps]; exact aemeasurable_id) (by fun_prop)
  rw [map_eps, variance_id_gaussianReal] at this
  simpa using this.symm

lemma cov_eps_eps (p q : Fin M × ℕ) (h : p ≠ q) :
    cov[fun ω : TrialSpace M => ω.2 p, fun ω => ω.2 q; trialMeasure I] = 0 := by
  have hind : iIndepFun (fun (r : Fin M × ℕ) (w : Fin M × ℕ → ℝ) => w r)
      (Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1) :=
    iIndepFun_infinitePi (P := fun _ : Fin M × ℕ => gaussianReal 0 1) (X := fun _ x => x)
      (fun _ => measurable_id)
  have h1 : MemLp (fun w : Fin M × ℕ → ℝ => w p) 2
      (Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1) := by
    have : MemLp (fun x : ℝ => x) 2 ((Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1).map
        (fun w : Fin M × ℕ → ℝ => w p)) := by
      rw [Measure.infinitePi_map_eval]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_pi_apply _).aemeasurable).1 this
  have h2 : MemLp (fun w : Fin M × ℕ → ℝ => w q) 2
      (Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1) := by
    have : MemLp (fun x : ℝ => x) 2 ((Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1).map
        (fun w : Fin M × ℕ → ℝ => w q)) := by
      rw [Measure.infinitePi_map_eval]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_pi_apply _).aemeasurable).1 this
  have h0 := (hind.indepFun h).covariance_eq_zero h1 h2
  have e := covariance_map (μ := trialMeasure I) (Z := Prod.snd)
    (X := fun w : Fin M × ℕ → ℝ => w p) (Y := fun w : Fin M × ℕ → ℝ => w q)
    (measurable_pi_apply _).aestronglyMeasurable (measurable_pi_apply _).aestronglyMeasurable
    (by fun_prop)
  rw [map_snd_trial, h0] at e
  exact e.symm

lemma cov_theta_eps (j : Fin M) (p : Fin M × ℕ) :
    cov[fun ω : TrialSpace M => theta ω j, fun ω => ω.2 p; trialMeasure I] = 0 := by
  have hind : IndepFun (fun ω : TrialSpace M => theta ω j) (fun ω => ω.2 p) (trialMeasure I) := by
    unfold trialMeasure theta
    exact indepFun_prod (X := fun x : EuclideanSpace ℝ (Fin M) => x j)
      (Y := fun w : Fin M × ℕ → ℝ => w p) (by fun_prop) (by fun_prop)
  exact hind.covariance_eq_zero (memLp_theta I j) (memLp_eps I p)

end PmC


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace PmC
open PmB

variable {M : ℕ} (I : Instance M)

/-! ### Covariance structure along a fixed allocation sequence -/

def idx (α : ℕ → Fin M) (s : ℕ) : Fin M × ℕ := (α s, cnt α s (α s))

lemma cnt_succ_apply (α : ℕ → Fin M) (t : ℕ) (a : Fin M) :
    cnt α (t + 1) a = if a = α t then cnt α t a + 1 else cnt α t a := by
  show Function.update (cnt α t) (α t) (cnt α t (α t) + 1) a = _
  by_cases h : a = α t
  · subst h; simp
  · simp [Function.update_of_ne h, h]

lemma cnt_mono (α : ℕ → Fin M) (a : Fin M) {s t : ℕ} (h : s ≤ t) : cnt α s a ≤ cnt α t a := by
  induction t with
  | zero => have : s = 0 := by omega
            subst this; exact le_rfl
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hs | hs
    · have := ih (by omega)
      rw [cnt_succ_apply]; split_ifs <;> omega
    · have : s = t + 1 := by omega
      subst this; exact le_rfl

lemma cnt_le (α : ℕ → Fin M) (t : ℕ) (a : Fin M) : cnt α t a ≤ t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => rw [cnt_succ_apply]; split_ifs <;> omega

lemma idx_ne (α : ℕ → Fin M) {s s' : ℕ} (h : s < s') : idx α s ≠ idx α s' := by
  intro heq
  simp only [idx, Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  have h3 : cnt α (s + 1) (α s) = cnt α s (α s) + 1 := by rw [cnt_succ_apply]; simp
  have h4 := cnt_mono α (α s) (show s + 1 ≤ s' by omega)
  rw [h1] at h2 h4 h3
  omega

noncomputable def R (α : ℕ → Fin M) (t : ℕ) (ω : TrialSpace M) (j : Fin M) : ℝ :=
  theta ω j - (kal I α t (Zα I α ω)).1 j

noncomputable def cc (α : ℕ → Fin M) (t : ℕ) (j : Fin M) : ℝ :=
  SigA I α t j (α t) / (I.lam (α t) + SigA I α t (α t) (α t))

lemma Zα_eq (α : ℕ → Fin M) (ω : TrialSpace M) (s : ℕ) :
    Zα I α ω s = theta ω (α s) + Real.sqrt (I.lam (α s)) * ω.2 (idx α s) := rfl

lemma R_succ (α : ℕ → Fin M) (t : ℕ) (ω : TrialSpace M) (j : Fin M) :
    R I α (t + 1) ω j = R I α t ω j - cc I α t j *
      (R I α t ω (α t) + Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) := by
  unfold R cc
  rw [kal_succ_fst, Zα_eq]
  have hd : I.lam (α t) + SigA I α t (α t) (α t) ≠ 0 := by
    have := (SigA_posDef I α t).diag_pos (i := α t)
    have := I.lam_pos (α t)
    linarith
  field_simp
  ring

lemma R_zero (α : ℕ → Fin M) (ω : TrialSpace M) (j : Fin M) : R I α 0 ω j = theta ω j - I.mu0 j :=
  rfl

lemma cov_R_succ (α : ℕ → Fin M) (t : ℕ) (X : TrialSpace M → ℝ) (hX : MemLp X 2 (trialMeasure I))
    (hR : ∀ j, MemLp (fun ω => R I α t ω j) 2 (trialMeasure I)) (j : Fin M) :
    cov[fun ω => R I α (t + 1) ω j, X; trialMeasure I] =
      cov[fun ω => R I α t ω j, X; trialMeasure I] - cc I α t j *
        (cov[fun ω => R I α t ω (α t), X; trialMeasure I] +
          Real.sqrt (I.lam (α t)) * cov[fun ω => ω.2 (idx α t), X; trialMeasure I]) := by
  have e : (fun ω => R I α (t + 1) ω j) = fun ω => R I α t ω j - cc I α t j *
      (R I α t ω (α t) + Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) := funext fun ω => R_succ I α t ω j
  rw [e]
  have h1 := hR (α t)
  have h2 : MemLp (fun ω : TrialSpace M => Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) 2
      (trialMeasure I) := (memLp_eps I _).const_mul _
  have h3 : MemLp (fun ω => R I α t ω (α t) + Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) 2
      (trialMeasure I) := h1.add h2
  rw [covariance_fun_sub_left (hR j) (h3.const_mul _) hX, covariance_const_mul_left]
  have e2 : cov[fun ω => R I α t ω (α t) + Real.sqrt (I.lam (α t)) * ω.2 (idx α t), X;
      trialMeasure I] = cov[fun ω => R I α t ω (α t), X; trialMeasure I] +
        cov[fun ω : TrialSpace M => Real.sqrt (I.lam (α t)) * ω.2 (idx α t), X; trialMeasure I] :=
    covariance_add_left h1 h2 hX
  rw [e2, covariance_const_mul_left]

lemma memLp_R (α : ℕ → Fin M) (t : ℕ) (j : Fin M) :
    MemLp (fun ω => R I α t ω j) 2 (trialMeasure I) := by
  induction t generalizing j with
  | zero => exact (memLp_theta I j).sub (memLp_const _)
  | succ t ih =>
    have e : (fun ω => R I α (t + 1) ω j) = fun ω => R I α t ω j - cc I α t j *
        (R I α t ω (α t) + Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) :=
      funext fun ω => R_succ I α t ω j
    rw [e]
    exact (ih j).sub (((ih (α t)).add ((memLp_eps I _).const_mul _)).const_mul _)

lemma sym_SigA (α : ℕ → Fin M) (t : ℕ) (a b : Fin M) : SigA I α t a b = SigA I α t b a :=
  CtMat.sym_of (SigA_posDef I α t).1 a b

lemma SigA_succ_apply (α : ℕ → Fin M) (t : ℕ) (j k : Fin M) :
    SigA I α (t + 1) j k = SigA I α t j k - SigA I α t j (α t) * SigA I α t (α t) k /
      (I.lam (α t) + SigA I α t (α t) (α t)) := by
  rw [SigA_succ]; rfl

/-- The covariance invariants of the Kalman residual along a fixed allocation sequence. -/
lemma invariants (α : ℕ → Fin M) (t : ℕ) :
    (∀ j k, cov[fun ω => R I α t ω j, fun ω => theta ω k; trialMeasure I] = SigA I α t j k) ∧
    (∀ j p, (∀ s < t, idx α s ≠ p) →
      cov[fun ω => R I α t ω j, fun ω => ω.2 p; trialMeasure I] = 0) ∧
    (∀ j k, cov[fun ω => R I α t ω j, fun ω => R I α t ω k; trialMeasure I] = SigA I α t j k) ∧
    (∀ j, ∀ s < t, cov[fun ω => R I α t ω j, fun ω => Zα I α ω s; trialMeasure I] = 0) ∧
    (∀ j, ∫ ω, R I α t ω j ∂(trialMeasure I) = 0) := by
  set P := trialMeasure I
  have hZ : ∀ s, MemLp (fun ω => Zα I α ω s) 2 P := fun s =>
    (memLp_theta I _).add ((memLp_eps I _).const_mul _)
  have covZ : ∀ (X : TrialSpace M → ℝ), MemLp X 2 P → ∀ s,
      cov[X, fun ω => Zα I α ω s; P] = cov[X, fun ω => theta ω (α s); P] +
        Real.sqrt (I.lam (α s)) * cov[X, fun ω => ω.2 (idx α s); P] := by
    intro X hX s
    calc cov[X, fun ω => Zα I α ω s; P]
        = cov[X, (fun ω => theta ω (α s)) +
            (fun ω : TrialSpace M => Real.sqrt (I.lam (α s)) * ω.2 (idx α s)); P] := rfl
      _ = cov[X, fun ω => theta ω (α s); P] +
            cov[X, fun ω : TrialSpace M => Real.sqrt (I.lam (α s)) * ω.2 (idx α s); P] :=
          covariance_add_right hX (memLp_theta I _) ((memLp_eps I _).const_mul _)
      _ = _ := by rw [covariance_const_mul_right]
  induction t with
  | zero =>
    have e : ∀ j, (fun ω => R I α 0 ω j) = fun ω => theta ω j - I.mu0 j := fun j => rfl
    have hθi : ∀ j, Integrable (fun ω => theta ω j) P :=
      fun j => (memLp_theta I j).integrable one_le_two
    refine ⟨fun j k => ?_, fun j p _ => ?_, fun j k => ?_, fun j s hs => absurd hs (by omega),
      fun j => ?_⟩
    · rw [e, covariance_sub_const_left (hθi j), cov_theta_theta]; rfl
    · rw [e, covariance_sub_const_left (hθi j), cov_theta_eps]
    · rw [e, e, covariance_sub_const_left (hθi j), covariance_comm,
        covariance_sub_const_left (hθi k), cov_theta_theta, CtMat.sym_of I.posDef.1]; rfl
    · rw [e, integral_sub (hθi j) (integrable_const _), integral_theta]; simp
  | succ t ih =>
    obtain ⟨hv, hiv, hii, hi, hiii⟩ := ih
    have hR := memLp_R I α t
    have hR' := memLp_R I α (t + 1)
    have hd : 0 < I.lam (α t) + SigA I α t (α t) (α t) := by
      have := (SigA_posDef I α t).diag_pos (i := α t); have := I.lam_pos (α t); linarith
    have hd' := hd.ne'
    have hl := I.lam_pos (α t)
    have hsq : Real.sqrt (I.lam (α t)) * Real.sqrt (I.lam (α t)) = I.lam (α t) :=
      Real.mul_self_sqrt hl.le
    have hn_unused : ∀ s < t, idx α s ≠ idx α t := fun s hs => idx_ne α hs
    have hRn : ∀ j, cov[fun ω => R I α t ω j, fun ω => ω.2 (idx α t); P] = 0 :=
      fun j => hiv j (idx α t) hn_unused
    -- (v)
    have hv' : ∀ j k, cov[fun ω => R I α (t + 1) ω j, fun ω => theta ω k; P] =
        SigA I α (t + 1) j k := by
      intro j k
      rw [cov_R_succ I α t _ (memLp_theta I k) hR, hv, hv, covariance_comm, cov_theta_eps,
        SigA_succ_apply]
      unfold cc
      ring
    -- (iv)
    have hiv' : ∀ j p, (∀ s < t + 1, idx α s ≠ p) →
        cov[fun ω => R I α (t + 1) ω j, fun ω => ω.2 p; P] = 0 := by
      intro j p hp
      have hp1 : ∀ s < t, idx α s ≠ p := fun s hs => hp s (by omega)
      have hp2 : idx α t ≠ p := hp t (by omega)
      rw [cov_R_succ I α t _ (memLp_eps I p) hR, hiv j p hp1, hiv (α t) p hp1,
        cov_eps_eps I _ p hp2]
      ring
    have hR'n : ∀ j, cov[fun ω => R I α (t + 1) ω j, fun ω => ω.2 (idx α t); P] =
        -(cc I α t j * Real.sqrt (I.lam (α t))) := by
      intro j
      rw [cov_R_succ I α t _ (memLp_eps I _) hR, hRn, hRn, var_eps]
      ring
    have hRR' : ∀ a k, cov[fun ω => R I α t ω a, fun ω => R I α (t + 1) ω k; P] =
        SigA I α t k a - cc I α t k * SigA I α t (α t) a := by
      intro a k
      rw [covariance_comm, cov_R_succ I α t _ (hR a) hR, hii, hii,
        covariance_comm (fun ω : TrialSpace M => ω.2 (idx α t)), hRn]
      ring
    have hεR' : ∀ k, cov[fun ω => ω.2 (idx α t), fun ω => R I α (t + 1) ω k; P] =
        -(cc I α t k * Real.sqrt (I.lam (α t))) := by
      intro k; rw [covariance_comm, hR'n]
    refine ⟨hv', hiv', fun j k => ?_, fun j s hs => ?_, fun j => ?_⟩
    · -- (ii)
      rw [cov_R_succ I α t _ (hR' k) hR, hRR', hRR', hεR', SigA_succ_apply,
        sym_SigA I α t k j, sym_SigA I α t (α t) j, sym_SigA I α t k (α t)]
      unfold cc
      field_simp
      simp only [Real.sq_sqrt hl.le, hsq]
      ring
    · -- (i)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | hs
      · have hεZ : cov[fun ω => ω.2 (idx α t), fun ω => Zα I α ω s; P] = 0 := by
          rw [covZ _ (memLp_eps I _), covariance_comm, cov_theta_eps,
            cov_eps_eps I _ _ (Ne.symm (idx_ne α hs))]
          ring
        rw [cov_R_succ I α t _ (hZ s) hR, hi j s hs, hi (α t) s hs, hεZ]
        ring
      · subst hs
        rw [covZ _ (hR' j), hv', hR'n, SigA_succ_apply]
        unfold cc
        field_simp
        simp only [Real.sq_sqrt hl.le, hsq]
        ring
    · -- (iii)
      have e : (fun ω => R I α (t + 1) ω j) = fun ω => R I α t ω j - cc I α t j *
          (R I α t ω (α t) + Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) :=
        funext fun ω => R_succ I α t ω j
      have hi1 := (hR j).integrable one_le_two
      have hi2 := (hR (α t)).integrable one_le_two
      have hi3 : Integrable (fun ω : TrialSpace M => Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) P :=
        ((memLp_eps I _).integrable one_le_two).const_mul _
      have hi23 : Integrable (fun ω => R I α t ω (α t) +
          Real.sqrt (I.lam (α t)) * ω.2 (idx α t)) P := hi2.add hi3
      rw [e, integral_sub hi1 (hi23.const_mul _), integral_const_mul,
        integral_add hi2 hi3, integral_const_mul, hiii, hiii, integral_eps]
      ring

end PmC


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace PmC
open PmB

variable {M : ℕ} (I : Instance M)

/-! ### Gaussianity -/

lemma hasGaussianLaw_add_const {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {X : Ω → E} (hX : HasGaussianLaw X P) (c : E) : HasGaussianLaw (fun ω => X ω + c) P where
  isGaussian_map := by
    have := hX.isGaussian_map
    have e : (P.map X).map (fun x => x + c) = P.map (fun ω => X ω + c) :=
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX.aemeasurable
    rw [← e]; infer_instance

abbrev EB (M T : ℕ) := (Fin M → ℝ) × (Fin M × Fin T → ℝ)

/-- The finite-dimensional Gaussian base vector: `θ` and the first `T` noises of every arm. -/
noncomputable def Bv (T : ℕ) (ω : TrialSpace M) : EB M T :=
  (fun j => theta ω j, fun p => ω.2 (p.1, (p.2 : ℕ)))

lemma hasGaussianLaw_theta : HasGaussianLaw (fun ω : TrialSpace M => fun j => theta ω j)
    (trialMeasure I) := by
  have h1 : HasGaussianLaw (fun ω : TrialSpace M => ω.1) (trialMeasure I) :=
    { isGaussian_map := by
        show IsGaussian ((trialMeasure I).map Prod.fst)
        rw [map_fst_trial]; infer_instance }
  exact h1.map_fun (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin M => ℝ)).toContinuousLinearMap

lemma hasGaussianLaw_eps (T : ℕ) :
    HasGaussianLaw (fun (ω : TrialSpace M) (p : Fin M × Fin T) => ω.2 (p.1, (p.2 : ℕ)))
      (trialMeasure I) := by
  set ν := Measure.infinitePi fun _ : Fin M × ℕ => gaussianReal 0 1
  have hind : iIndepFun (fun (r : Fin M × ℕ) (w : Fin M × ℕ → ℝ) => w r) ν :=
    iIndepFun_infinitePi (P := fun _ : Fin M × ℕ => gaussianReal 0 1) (X := fun _ x => x)
      (fun _ => measurable_id)
  have hg : Function.Injective (fun p : Fin M × Fin T => (p.1, (p.2 : ℕ))) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.ext h.2)
  have hind' := hind.precomp hg
  have hgl : ∀ r : Fin M × ℕ, HasGaussianLaw (fun w : Fin M × ℕ → ℝ => w r) ν := fun r =>
    { isGaussian_map := by
        show IsGaussian (ν.map (fun w : Fin M × ℕ → ℝ => w r))
        rw [Measure.infinitePi_map_eval]; infer_instance }
  have h1 : HasGaussianLaw (fun (w : Fin M × ℕ → ℝ) (p : Fin M × Fin T) => w (p.1, (p.2 : ℕ))) ν :=
    iIndepFun.hasGaussianLaw (fun p => hgl _) hind'
  refine { isGaussian_map := ?_ }
  have := h1.isGaussian_map
  have e : (trialMeasure I).map (fun (ω : TrialSpace M) (p : Fin M × Fin T) => ω.2 (p.1, (p.2 : ℕ)))
      = ν.map (fun (w : Fin M × ℕ → ℝ) (p : Fin M × Fin T) => w (p.1, (p.2 : ℕ))) := by
    rw [show ν = (trialMeasure I).map Prod.snd from (map_snd_trial I).symm,
      Measure.map_map (by fun_prop) measurable_snd]; rfl
  rw [e]; exact this

lemma hasGaussianLaw_Bv (T : ℕ) : HasGaussianLaw (Bv T) (trialMeasure I) := by
  have hind : IndepFun (fun ω : TrialSpace M => fun j => theta ω j)
      (fun (ω : TrialSpace M) (p : Fin M × Fin T) => ω.2 (p.1, (p.2 : ℕ))) (trialMeasure I) := by
    unfold trialMeasure theta
    exact indepFun_prod (X := fun (x : EuclideanSpace ℝ (Fin M)) (j : Fin M) => x j)
      (Y := fun (w : Fin M × ℕ → ℝ) (p : Fin M × Fin T) => w (p.1, (p.2 : ℕ)))
      (by fun_prop) (by fun_prop)
  exact IndepFun.hasGaussianLaw (hasGaussianLaw_theta I) (hasGaussianLaw_eps I T) hind

noncomputable def pθ (T : ℕ) (j : Fin M) : StrongDual ℝ (EB M T) :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ _ _)

noncomputable def pε (T : ℕ) (q : Fin M × Fin T) : StrongDual ℝ (EB M T) :=
  (ContinuousLinearMap.proj q).comp (ContinuousLinearMap.snd ℝ _ _)

lemma pθ_apply (T : ℕ) (j : Fin M) (ω : TrialSpace M) : pθ T j (Bv T ω) = theta ω j := rfl

lemma pε_apply (T : ℕ) (q : Fin M × Fin T) (ω : TrialSpace M) :
    pε T q (Bv T ω) = ω.2 (q.1, (q.2 : ℕ)) := rfl

/-- The residual is an affine function of the base vector. -/
lemma R_affine (α : ℕ → Fin M) (T : ℕ) : ∀ t ≤ T, ∃ (L : Fin M → StrongDual ℝ (EB M T))
    (κ : Fin M → ℝ), ∀ ω j, R I α t ω j = L j (Bv T ω) + κ j := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun j => pθ T j, fun j => -I.mu0 j, fun ω j => by
      rw [R_zero, pθ_apply]; ring⟩
  | succ t ih =>
    intro ht
    obtain ⟨L, κ, hL⟩ := ih (by omega)
    have hk : cnt α t (α t) < T := lt_of_le_of_lt (cnt_le α t _) (by omega)
    let q : Fin M × Fin T := (α t, ⟨cnt α t (α t), hk⟩)
    refine ⟨fun j => L j - cc I α t j • (L (α t) + Real.sqrt (I.lam (α t)) • pε T q),
      fun j => κ j - cc I α t j * κ (α t), fun ω j => ?_⟩
    rw [R_succ, hL, hL]
    have : ω.2 (idx α t) = pε T q (Bv T ω) := rfl
    rw [this]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, smul_eq_mul]
    ring

lemma Zα_affine (α : ℕ → Fin M) (T : ℕ) (s : Fin T) :
    ∃ L : StrongDual ℝ (EB M T), ∀ ω, Zα I α ω s = L (Bv T ω) := by
  have hk : cnt α s (α s) < T := lt_of_le_of_lt (cnt_le α s _) s.2
  refine ⟨pθ T (α s) + Real.sqrt (I.lam (α s)) • pε T (α s, ⟨cnt α s (α s), hk⟩), fun ω => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    pθ_apply, pε_apply]
  rfl

/-- Independence of the final residual and the observations. -/
lemma indep_R_Z (α : ℕ → Fin M) (T : ℕ) (i : Fin M) :
    IndepFun (fun ω (_ : Unit) => R I α T ω i) (fun ω (s : Fin T) => Zα I α ω s)
      (trialMeasure I) := by
  obtain ⟨L, κ, hL⟩ := R_affine I α T T le_rfl
  choose Lz hLz using Zα_affine I α T
  let A : EB M T →L[ℝ] (Unit → ℝ) × (Fin T → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Unit => L i).prod (ContinuousLinearMap.pi fun s => Lz s)
  have hG : HasGaussianLaw (fun ω => A (Bv T ω) + ((fun _ : Unit => κ i), (0 : Fin T → ℝ)))
      (trialMeasure I) :=
    hasGaussianLaw_add_const ((hasGaussianLaw_Bv I T).map_fun A) _
  have e : (fun ω => A (Bv T ω) + ((fun _ : Unit => κ i), (0 : Fin T → ℝ))) =
      fun ω => ((fun _ : Unit => R I α T ω i), (fun s : Fin T => Zα I α ω s)) := by
    funext ω
    refine Prod.ext ?_ ?_
    · funext u; simp [A, hL]
    · funext s; simp [A, hLz]
  rw [e] at hG
  exact HasGaussianLaw.indepFun_of_covariance_eval
    (X := fun (_ : Unit) ω => R I α T ω i) (Y := fun (s : Fin T) ω => Zα I α ω s) hG
    (fun _ s => ((invariants I α T).2.2.2.1 i s s.2))

/-! ### The two integral identities -/

lemma setIntegral_theta (α : ℕ → Fin M) (T : ℕ) (i : Fin M) (C : Set (Fin T → ℝ))
    (hC : MeasurableSet C) :
    ∫ ω in (fun ω (s : Fin T) => Zα I α ω s) ⁻¹' C, theta ω i ∂(trialMeasure I) =
      ∫ ω in (fun ω (s : Fin T) => Zα I α ω s) ⁻¹' C, (kal I α T (Zα I α ω)).1 i
        ∂(trialMeasure I) := by
  set P := trialMeasure I
  set Zv := fun ω (s : Fin T) => Zα I α ω s
  have hZv : Measurable Zv := measurable_pi_iff.2 fun s => measurable_Zα I α s
  have hS : MeasurableSet (Zv ⁻¹' C) := hZv hC
  have hRm := memLp_R I α T i
  have hRi : Integrable (fun ω => R I α T ω i) P := hRm.integrable one_le_two
  have hθi : Integrable (fun ω => theta ω i) P := (memLp_theta I i).integrable one_le_two
  have hk : Integrable (fun ω => (kal I α T (Zα I α ω)).1 i) P := by
    have : (fun ω => (kal I α T (Zα I α ω)).1 i) = fun ω => theta ω i - R I α T ω i := by
      funext ω; simp [R]
    rw [this]; exact hθi.sub hRi
  have hsplit : ∀ ω, theta ω i = (kal I α T (Zα I α ω)).1 i + R I α T ω i := fun ω => by
    simp [R]
  have h0 : ∫ ω in Zv ⁻¹' C, R I α T ω i ∂P = 0 := by
    rw [← integral_indicator hS]
    have e : (Zv ⁻¹' C).indicator (fun ω => R I α T ω i) =
        fun ω => (C.indicator (fun _ => (1 : ℝ)) (Zv ω)) * R I α T ω i := by
      funext ω
      by_cases h : ω ∈ Zv ⁻¹' C
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show Zv ω ∈ C from h), one_mul]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show Zv ω ∉ C from h), zero_mul]
    rw [e]
    have hind : IndepFun (fun ω => C.indicator (fun _ => (1 : ℝ)) (Zv ω))
        (fun ω => R I α T ω i) P :=
      (indep_R_Z I α T i).symm.comp (φ := C.indicator (fun _ => (1 : ℝ)))
        (ψ := fun v : Unit → ℝ => v ()) (measurable_const.indicator hC) (measurable_pi_apply ())
    rw [hind.integral_fun_mul_eq_mul_integral
      ((measurable_const.indicator hC).comp hZv).aestronglyMeasurable
      hRm.aestronglyMeasurable]
    rw [(invariants I α T).2.2.2.2 i, mul_zero]
  rw [show (fun ω => theta ω i) = fun ω => (kal I α T (Zα I α ω)).1 i + R I α T ω i from
    funext hsplit, integral_add hk.integrableOn hRi.integrableOn, h0, add_zero]

lemma setIntegral_sq (α : ℕ → Fin M) (T : ℕ) (i : Fin M) (C : Set (Fin T → ℝ))
    (hC : MeasurableSet C) :
    ∫ ω in (fun ω (s : Fin T) => Zα I α ω s) ⁻¹' C,
        (theta ω i - (kal I α T (Zα I α ω)).1 i) ^ 2 ∂(trialMeasure I) =
      ∫ ω in (fun ω (s : Fin T) => Zα I α ω s) ⁻¹' C, SigA I α T i i ∂(trialMeasure I) := by
  set P := trialMeasure I
  set Zv := fun ω (s : Fin T) => Zα I α ω s
  have hZv : Measurable Zv := measurable_pi_iff.2 fun s => measurable_Zα I α s
  have hS : MeasurableSet (Zv ⁻¹' C) := hZv hC
  have hRm := memLp_R I α T i
  have e1 : ∀ ω, (theta ω i - (kal I α T (Zα I α ω)).1 i) ^ 2 = R I α T ω i ^ 2 := fun ω => rfl
  simp_rw [e1]
  rw [← integral_indicator hS]
  have e : (Zv ⁻¹' C).indicator (fun ω => R I α T ω i ^ 2) =
      fun ω => (C.indicator (fun _ => (1 : ℝ)) (Zv ω)) * R I α T ω i ^ 2 := by
    funext ω
    by_cases h : ω ∈ Zv ⁻¹' C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show Zv ω ∈ C from h), one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show Zv ω ∉ C from h), zero_mul]
  rw [e]
  have hind : IndepFun (fun ω => C.indicator (fun _ => (1 : ℝ)) (Zv ω))
      (fun ω => R I α T ω i ^ 2) P :=
    (indep_R_Z I α T i).symm.comp (φ := C.indicator (fun _ => (1 : ℝ)))
      (ψ := fun v : Unit → ℝ => v () ^ 2) (measurable_const.indicator hC)
      ((measurable_pi_apply ()).pow_const 2)
  rw [hind.integral_fun_mul_eq_mul_integral
    ((measurable_const.indicator hC).comp hZv).aestronglyMeasurable
    (hRm.aestronglyMeasurable.pow 2)]
  have hvar : ∫ ω, R I α T ω i ^ 2 ∂P = SigA I α T i i := by
    have h1 := variance_eq_integral hRm.aemeasurable
    rw [(invariants I α T).2.2.2.2 i] at h1
    have h2 : Var[fun ω => R I α T ω i; P] = SigA I α T i i := by
      rw [← covariance_self hRm.aemeasurable]; exact (invariants I α T).2.2.1 i i
    rw [← h2, h1]
    simp only [sub_zero]; rfl
  rw [hvar, setIntegral_const, smul_eq_mul, ← integral_indicator_one hS]
  rfl

end PmC


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace PmD
open PmB PmC

variable {M : ℕ} (I : Instance M)

/-- The history events, indexed by finite allocation histories. -/
def Ha (T : ℕ) (a : Fin T → Fin M) : Set (TrialSpace M) := Hset I (extA (hM0 I) a) T

lemma measurableSet_Ha (T : ℕ) (a : Fin T → Fin M) : MeasurableSet (Ha I T a) := by
  unfold Ha; rw [Hset_eq]
  exact (measurable_pi_iff.2 fun s => measurable_Zα I _ s) (measurableSet_Dset I _ T)

lemma Ha_disjoint (T : ℕ) : Pairwise (Function.onFun Disjoint (Ha I T)) := by
  intro a b hab
  rw [Function.onFun, Set.disjoint_left]
  intro ω ha hb
  apply hab
  funext s
  have h1 := ha s s.2
  have h2 := hb s s.2
  rw [h1] at h2
  simpa [extA, s.2] using h2

lemma mem_Ha_self (T : ℕ) (ω : TrialSpace M) :
    ω ∈ Ha I T (fun s : Fin T => alloc I s ω) := by
  intro s hs; simp [extA, hs]

lemma iUnion_Ha (T : ℕ) : ⋃ a, Ha I T a = Set.univ :=
  Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨_, mem_Ha_self I T ω⟩

/-- The observation vector. -/
noncomputable def obsT (T : ℕ) (ω : TrialSpace M) : Fin T → ℝ := fun s => obsN I ω s

lemma measurable_obsT (T : ℕ) : Measurable (obsT I T) :=
  measurable_pi_iff.2 fun s => measurable_obsN I s

noncomputable def Zv (T : ℕ) (a : Fin T → Fin M) (ω : TrialSpace M) : Fin T → ℝ :=
  fun s => Zα I (extA (hM0 I) a) ω s

lemma piece_eq (T : ℕ) (a : Fin T → Fin M) (B : Set (Fin T → ℝ)) :
    obsT I T ⁻¹' B ∩ Ha I T a =
      Zv I T a ⁻¹' (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}) := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  have key : ∀ (h : ω ∈ Ha I T a), obsT I T ω = Zv I T a ω := fun h => by
    funext s; exact obsN_eq_Z I _ T ω h s s.2
  have hiff : ω ∈ Ha I T a ↔ extY T (Zv I T a ω) ∈ Dset I (extA (hM0 I) a) T := by
    unfold Ha; rw [Hset_eq]
    simp only [Set.mem_preimage]
    exact Dset_congr I _ T _ _ (fun s hs => by simp [extY, Zv, hs])
  constructor
  · rintro ⟨hB, hH⟩
    exact ⟨by rw [← key hH]; exact hB, hiff.1 hH⟩
  · rintro ⟨hB, hD⟩
    have hH := hiff.2 hD
    exact ⟨by rw [key hH]; exact hB, hH⟩

lemma measurableSet_C (T : ℕ) (a : Fin T → Fin M) (B : Set (Fin T → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}) :=
  hB.inter ((measurable_extY T) (measurableSet_Dset I _ T))

lemma setIntegral_decomp (T : ℕ) (f : TrialSpace M → ℝ) (hf : Integrable f (trialMeasure I))
    (s : Set (TrialSpace M)) (hs : MeasurableSet s) :
    ∫ ω in s, f ω ∂(trialMeasure I) = ∑ a, ∫ ω in s ∩ Ha I T a, f ω ∂(trialMeasure I) := by
  have hU : s = ⋃ a, s ∩ Ha I T a := by
    rw [← Set.inter_iUnion, iUnion_Ha, Set.inter_univ]
  conv_lhs => rw [hU]
  refine integral_iUnion_fintype (fun a => hs.inter (measurableSet_Ha I T a)) ?_
    (fun a => hf.integrableOn)
  intro a b hab
  exact ((Ha_disjoint I T hab).mono Set.inter_subset_right Set.inter_subset_right)

lemma mu_on_Ha (T : ℕ) (a : Fin T → Fin M) (ω : TrialSpace M) (h : ω ∈ Ha I T a) (i : Fin M) :
    mu I T ω i = (kal I (extA (hM0 I) a) T (Zα I (extA (hM0 I) a) ω)).1 i := by
  rw [(mu_eq_on_H I _ T ω h).1]

lemma Sig_on_Ha (T : ℕ) (a : Fin T → Fin M) (ω : TrialSpace M) (h : ω ∈ Ha I T a) :
    Sig I T ω = SigA I (extA (hM0 I) a) T := (mu_eq_on_H I _ T ω h).2

lemma integrable_kal (α : ℕ → Fin M) (T : ℕ) (i : Fin M) :
    Integrable (fun ω => (kal I α T (Zα I α ω)).1 i) (trialMeasure I) := by
  have : (fun ω => (kal I α T (Zα I α ω)).1 i) = fun ω => theta ω i - R I α T ω i := by
    funext ω; simp [R]
  rw [this]
  exact ((memLp_theta I i).integrable one_le_two).sub ((memLp_R I α T i).integrable one_le_two)

lemma integrable_R_sq (α : ℕ → Fin M) (T : ℕ) (i : Fin M) :
    Integrable (fun ω => R I α T ω i ^ 2) (trialMeasure I) :=
  (memLp_R I α T i).integrable_sq

end PmD


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace PmE
open PmB PmC PmD

theorem main {M : ℕ} (I : Instance M) (T : ℕ) (i : Fin M) :
    Measurable (obsT I T) ∧
      StronglyMeasurable[MeasurableSpace.comap (obsT I T) inferInstance]
        (fun ω => mu I T ω i) ∧
      StronglyMeasurable[MeasurableSpace.comap (obsT I T) inferInstance]
        (fun ω => Sig I T ω i i) ∧
      (fun ω => mu I T ω i) =ᵐ[trialMeasure I]
        (trialMeasure I)[fun ω => theta ω i | MeasurableSpace.comap (obsT I T) inferInstance] ∧
      (fun ω => Sig I T ω i i) =ᵐ[trialMeasure I]
        (trialMeasure I)[fun ω => (theta ω i - mu I T ω i) ^ 2 |
          MeasurableSpace.comap (obsT I T) inferInstance] := by
  set P := trialMeasure I
  have hobs := measurable_obsT I T
  have hm : MeasurableSpace.comap (obsT I T) inferInstance ≤
      (inferInstance : MeasurableSpace (TrialSpace M)) := hobs.comap_le
  have hcm : Measurable[MeasurableSpace.comap (obsT I T) inferInstance] (obsT I T) :=
    comap_measurable (obsT I T)
  -- measurability
  have hmuF : StronglyMeasurable[MeasurableSpace.comap (obsT I T) inferInstance]
      (fun ω => mu I T ω i) := by
    have e : (fun ω => mu I T ω i) = (fun z => (rep I T (extY T z)).1 i) ∘ obsT I T := by
      funext ω; simp only [Function.comp_apply, mu]; rw [cpdeState_eq_ext]; rfl
    rw [e]
    exact ((((measurable_pi_apply i).comp (measurable_rep_fst I T)).comp
      (measurable_extY T)).comp hcm).stronglyMeasurable
  have hsigF : StronglyMeasurable[MeasurableSpace.comap (obsT I T) inferInstance]
      (fun ω => Sig I T ω i i) := by
    have e : (fun ω => Sig I T ω i i) = (fun z => (rep I T (extY T z)).2.1 i i) ∘ obsT I T := by
      funext ω; simp only [Function.comp_apply, Sig]; rw [cpdeState_eq_ext]; rfl
    rw [e]
    exact (((measurable_rep_sig I T i i).comp (measurable_extY T)).comp hcm).stronglyMeasurable
  -- integrability
  have hθm : Measurable fun ω : TrialSpace M => theta ω i := by unfold theta; fun_prop
  have hθint : Integrable (fun ω => theta ω i) P := (memLp_theta I i).integrable one_le_two
  have hmuint : Integrable (fun ω => mu I T ω i) P := by
    refine Integrable.mono' (g := fun ω => ∑ a : Fin T → Fin M,
        |(kal I (extA (hM0 I) a) T (Zα I (extA (hM0 I) a) ω)).1 i|)
      (integrable_finset_sum _ fun a _ => (integrable_kal I _ T i).abs)
      (hmuF.mono hm).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    have hω := mem_Ha_self I T ω
    rw [Real.norm_eq_abs, mu_on_Ha I T _ ω hω i]
    exact Finset.single_le_sum (f := fun a : Fin T → Fin M =>
        |(kal I (extA (hM0 I) a) T (Zα I (extA (hM0 I) a) ω)).1 i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  have hfint : Integrable (fun ω => (theta ω i - mu I T ω i) ^ 2) P := by
    refine Integrable.mono' (g := fun ω => ∑ a : Fin T → Fin M, R I (extA (hM0 I) a) T ω i ^ 2)
      (integrable_finset_sum _ fun a _ => integrable_R_sq I _ T i)
      ((hθm.sub ((hmuF.mono hm).measurable)).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have hω := mem_Ha_self I T ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mu_on_Ha I T _ ω hω i]
    exact Finset.single_le_sum (f := fun a : Fin T → Fin M => R I (extA (hM0 I) a) T ω i ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  have hsigint : Integrable (fun ω => Sig I T ω i i) P := by
    refine Integrable.mono' (g := fun _ => I.Sig0 i i) (integrable_const _)
      (hsigF.mono hm).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (CtSeq.sig_posDef I T ω).diag_pos]
    exact CtSeq.sig_diag_le I T ω i
  refine ⟨hobs, hmuF, hsigF, ?_, ?_⟩
  · refine ae_eq_condExp_of_forall_setIntegral_eq hm hθint (fun s _ _ => hmuint.integrableOn)
      (fun s hs _ => ?_) (hmuF.aestronglyMeasurable)
    obtain ⟨B, hB, rfl⟩ := hs
    have hs' : MeasurableSet (obsT I T ⁻¹' B) := hobs hB
    rw [setIntegral_decomp I T _ hmuint _ hs', setIntegral_decomp I T _ hθint _ hs']
    refine Finset.sum_congr rfl fun a _ => ?_
    have hp := piece_eq I T a B
    have hC := measurableSet_C I T a B hB
    have hZm : Measurable (Zv I T a) := measurable_pi_iff.2 fun s => measurable_Zα I _ s
    have h1 : ∫ ω in Zv I T a ⁻¹' (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}),
        mu I T ω i ∂P = ∫ ω in Zv I T a ⁻¹' (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}),
        (kal I (extA (hM0 I) a) T (Zα I (extA (hM0 I) a) ω)).1 i ∂P :=
      setIntegral_congr_fun (hZm hC) (fun ω hω => by
        rw [← hp] at hω; exact mu_on_Ha I T a ω hω.2 i)
    rw [hp, h1]
    exact (setIntegral_theta I (extA (hM0 I) a) T i _ hC).symm
  · refine ae_eq_condExp_of_forall_setIntegral_eq hm hfint (fun s _ _ => hsigint.integrableOn)
      (fun s hs _ => ?_) (hsigF.aestronglyMeasurable)
    obtain ⟨B, hB, rfl⟩ := hs
    have hs' : MeasurableSet (obsT I T ⁻¹' B) := hobs hB
    rw [setIntegral_decomp I T _ hsigint _ hs', setIntegral_decomp I T _ hfint _ hs']
    refine Finset.sum_congr rfl fun a _ => ?_
    have hp := piece_eq I T a B
    have hC := measurableSet_C I T a B hB
    have hZm : Measurable (Zv I T a) := measurable_pi_iff.2 fun s => measurable_Zα I _ s
    have h1 : ∫ ω in Zv I T a ⁻¹' (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}),
        Sig I T ω i i ∂P = ∫ ω in Zv I T a ⁻¹' (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}),
        SigA I (extA (hM0 I) a) T i i ∂P :=
      setIntegral_congr_fun (hZm hC) (fun ω hω => by
        rw [← hp] at hω; show Sig I T ω i i = _; rw [Sig_on_Ha I T a ω hω.2])
    have h2 : ∫ ω in Zv I T a ⁻¹' (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}),
        (theta ω i - mu I T ω i) ^ 2 ∂P =
        ∫ ω in Zv I T a ⁻¹' (B ∩ {z | extY T z ∈ Dset I (extA (hM0 I) a) T}),
        (theta ω i - (kal I (extA (hM0 I) a) T (Zα I (extA (hM0 I) a) ω)).1 i) ^ 2 ∂P :=
      setIntegral_congr_fun (hZm hC) (fun ω hω => by
        rw [← hp] at hω; show (theta ω i - mu I T ω i) ^ 2 = _
        rw [mu_on_Ha I T a ω hω.2 i])
    rw [hp, h1, h2]
    exact (setIntegral_sq I (extA (hM0 I) a) T i _ hC).symm

end PmE

theorem solution {M : ℕ} (I : Instance M) (T : ℕ) (i : Fin M) :
    Measurable (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) ∧
      StronglyMeasurable[MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance]
        (fun ω => mu I T ω i) ∧
      StronglyMeasurable[MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance]
        (fun ω => Sig I T ω i i) ∧
      (fun ω => mu I T ω i) =ᵐ[trialMeasure I]
        (trialMeasure I)[fun ω => theta ω i | MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance] ∧
      (fun ω => Sig I T ω i i) =ᵐ[trialMeasure I]
        (trialMeasure I)[fun ω => (theta ω i - mu I T ω i) ^ 2 | MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance] :=
  PmE.main I T i
