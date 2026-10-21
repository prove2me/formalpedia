-- Prove2me | solution 1 for CorrelatedTrials.Consistency.lemma_EC_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:49:27.510215+00:00
-- url     : https://prove2.me/submissions/3c712203-48f2-43cb-b8bd-f7e76107d957

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


namespace CtCore

variable {M : ℕ}

lemma memLp_lf (s : ℝ) {N : ℕ} (c : Option (Fin N) → ℝ) : MemLp (lf c) 2 (auxMeasure s) := by
  unfold lf
  exact memLp_finsetSum _ (fun j _ => (memLp_Yc s j).const_mul (c j))

lemma integral_sq_lf (s : ℝ) (hs : 0 ≤ s) {N : ℕ} (c : Option (Fin N) → ℝ) :
    ∫ ω, (lf c ω) ^ 2 ∂(auxMeasure s) = ∑ j, c j * c j * wt s j := by
  have h1 := variance_eq_sub (memLp_lf s c)
  rw [← covariance_self (memLp_lf s c).aemeasurable, lin_cov s hs, integral_lf] at h1
  simp only [Pi.pow_apply] at h1
  linarith

lemma integral_sq_Yc (s : ℝ) (hs : 0 ≤ s) {N : ℕ} (j : Option (Fin N)) :
    ∫ ω, (Yc j ω) ^ 2 ∂(auxMeasure s) = wt s j := by
  have h1 := variance_eq_sub (memLp_Yc s j)
  rw [← covariance_self (memLp_Yc s j).aemeasurable, cov_Yc_self s hs, integral_Yc] at h1
  simp only [Pi.pow_apply] at h1
  linarith

lemma vR (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (n : ℕ) :
    ∫ ω, (lf (cR l s n) ω) ^ 2 ∂(auxMeasure s) = l * s / (l + n * s) := by
  have hd : l + n * s ≠ 0 := by positivity
  rw [integral_sq_lf s hs.le, Fintype.sum_option]
  simp only [cR, wt, mul_one]
  have h2 : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  rw [h2]; ring

lemma indep_R (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (n : ℕ) :
    Indep (MeasurableSpace.comap (lf (cR l s n)) inferInstance) (auxFiltration l n)
      (auxMeasure s) := by
  have h := indep_lf s hs.le (cR l s n) (dS l n) (cov_cR_dS l s hl hs n)
  rw [auxFiltration_eq]
  have e : (fun ω (k : Set.Iic n) => lf (dS l n k) ω) = (fun ω (j : Set.Iic n) => auxSum l j ω) := by
    funext ω k; rw [auxSum_eq]
  rw [e] at h
  exact h

lemma indepFun_R (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (n : ℕ) {f : AuxSpace → ℝ}
    (hf : Measurable[auxFiltration l n] f) : IndepFun (lf (cR l s n)) f (auxMeasure s) :=
  indep_of_indep_of_le_right (indep_R l s hl hs n) hf.comap_le


lemma EZ2 (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (T : AuxSpace → WithTop ℕ)
    (hT : AdmissibleLookahead l T) :
    Integrable (fun ω => (stoppedValue (Zproc l s) T ω) ^ 2) (auxMeasure s) ∧
    ∫ ω, (stoppedValue (Zproc l s) T ω) ^ 2 ∂(auxMeasure s) ≤
      s ^ 2 / l * ∫ ω, (((T ω).untopA : ℕ) : ℝ) ∂(auxMeasure s) := by
  obtain ⟨N, hTfin, hTmeas, hTint, hT1⟩ := T_facts l s T hT
  have hst := hT.1
  set P := auxMeasure s with hP
  set A : ℕ → Set AuxSpace := fun n => {ω | T ω = n} with hAdef
  have hAF : ∀ n, MeasurableSet[auxFiltration l n] (A n) :=
    fun n => hst.measurableSet_eq_of_countable n
  have hA : ∀ n, MeasurableSet (A n) := fun n => (auxFiltration l).le n _ (hAF n)
  set u : ℕ → AuxSpace → ℝ := fun n => (A n).indicator (Zproc l s n) with hudef
  set w : ℕ → AuxSpace → ℝ := fun n => (A n).indicator (fun _ => (1 : ℝ)) with hwdef
  set R : ℕ → AuxSpace → ℝ := fun n => lf (cR l s n) with hRdef
  have hxiR : ∀ n ω, ω.1 = Zproc l s n ω + R n ω := fun n ω => by
    have := R_eq l s hl hs n ω
    simp only [hRdef]; linarith
  have hξ : MemLp (fun ω : AuxSpace => ω.1) 2 P := memLp_Yc s (N := 0) none
  have hR2 : ∀ n, MemLp (R n) 2 P := fun n => memLp_lf s _
  have hZ2 : ∀ n, MemLp (Zproc l s n) 2 P := fun n => by
    have : Zproc l s n = fun ω => ω.1 - R n ω := by
      funext ω; have := hxiR n ω; linarith
    rw [this]; exact hξ.sub (hR2 n)
  have hu2 : ∀ n, MemLp (u n) 2 P := fun n => (hZ2 n).indicator (hA n)
  -- per-n identity
  have hper : ∀ n, ∫ ω, (u n ω) ^ 2 ∂P =
      ∫ ω, (A n).indicator (fun ω : AuxSpace => ω.1 ^ 2) ω ∂P -
        (l * s / (l + n * s)) * ∫ ω, w n ω ∂P := by
    intro n
    have hpt : ∀ ω, (A n).indicator (fun ω : AuxSpace => ω.1 ^ 2) ω =
        (u n ω) ^ 2 + 2 * (R n ω * u n ω) + (R n ω ^ 2) * w n ω := by
      intro ω
      by_cases hω : ω ∈ A n
      · simp only [hudef, hwdef, Set.indicator_of_mem hω]
        rw [hxiR n ω]; ring
      · simp [hudef, hwdef, Set.indicator_of_notMem hω]
    have I1 : Integrable (fun ω => (u n ω) ^ 2) P := (hu2 n).integrable_sq
    have I2 : Integrable (fun ω => R n ω * u n ω) P := by
      have := (hR2 n).integrable_mul (hu2 n)
      exact this
    have I3 : Integrable (fun ω => (R n ω ^ 2) * w n ω) P := by
      have h := ((hR2 n).integrable_sq).indicator (hA n)
      refine h.congr (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ A n
      · simp [hwdef, Set.indicator_of_mem hω]
      · simp [hwdef, Set.indicator_of_notMem hω]
    have hum : Measurable[auxFiltration l n] (u n) :=
      (Zproc_sm l s n).measurable.indicator (hAF n)
    have hwm : Measurable[auxFiltration l n] (w n) :=
      measurable_const.indicator (hAF n)
    have hind1 := indepFun_R l s hl hs n hum
    have hind2 := (indepFun_R l s hl hs n hwm).comp (φ := fun x : ℝ => x ^ 2) (ψ := id)
      (measurable_id.pow_const 2) measurable_id
    have e1 : ∫ ω, R n ω * u n ω ∂P = 0 := by
      have := hind1.integral_mul_eq_mul_integral (meas_lf _).aestronglyMeasurable
        ((hu2 n).aestronglyMeasurable)
      simp only [hRdef] at this ⊢
      rw [show (fun ω => lf (cR l s n) ω * u n ω) = lf (cR l s n) * u n from rfl, this, integral_lf]
      simp
    have e2 : ∫ ω, (R n ω ^ 2) * w n ω ∂P = (l * s / (l + n * s)) * ∫ ω, w n ω ∂P := by
      have := hind2.integral_mul_eq_mul_integral
        ((meas_lf _).pow_const 2).aestronglyMeasurable
        ((measurable_const.indicator (hA n)).aestronglyMeasurable)
      simp only [hRdef, Function.comp_def, id] at this ⊢
      rw [show (fun ω => lf (cR l s n) ω ^ 2 * w n ω) =
        (fun ω => lf (cR l s n) ω ^ 2) * w n from rfl, this, vR l s hl hs n]
    have := integral_congr_ae (μ := P) (Eventually.of_forall hpt)
    have I12 : Integrable (fun ω => u n ω ^ 2 + 2 * (R n ω * u n ω)) P := I1.add (I2.const_mul 2)
    have I22 : Integrable (fun ω => 2 * (R n ω * u n ω)) P := I2.const_mul 2
    rw [this, integral_add I12 I3, integral_add I1 I22, integral_const_mul, e1, e2]
    ring
  -- summation over the values of T
  have hsum : ∀ (h : ℕ → AuxSpace → ℝ) (ω : AuxSpace),
      ∑ n ∈ Finset.range (N + 1), (A n).indicator (h n) ω = h ((T ω).untopA) ω := by
    intro h ω
    obtain ⟨m, hm, h1, h2⟩ := hTfin ω
    have hmem : m ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    rw [Finset.sum_eq_single m]
    · have : ω ∈ A m := by simp [hAdef, hm]
      rw [Set.indicator_of_mem this, hm]
      rfl
    · intro n _ hn
      have : ω ∉ A n := by
        simp only [hAdef, Set.mem_setOf_eq, hm]
        intro h'
        exact hn (by exact_mod_cast h'.symm)
      rw [Set.indicator_of_notMem this]
    · intro h'; exact absurd hmem h'
  have hind_sq : ∀ n ω, (u n ω) ^ 2 = (A n).indicator (fun ω => Zproc l s n ω ^ 2) ω := by
    intro n ω
    by_cases hω : ω ∈ A n
    · simp [hudef, Set.indicator_of_mem hω]
    · simp [hudef, Set.indicator_of_notMem hω]
  have hZT : ∀ ω, (stoppedValue (Zproc l s) T ω) ^ 2 = ∑ n ∈ Finset.range (N + 1), (u n ω) ^ 2 := by
    intro ω
    simp_rw [hind_sq]
    rw [hsum (fun n ω => Zproc l s n ω ^ 2) ω]
    rfl
  have hI1 : ∀ n, Integrable (fun ω => (u n ω) ^ 2) P := fun n => (hu2 n).integrable_sq
  have hIxi : ∀ n, Integrable ((A n).indicator (fun ω : AuxSpace => ω.1 ^ 2)) P :=
    fun n => hξ.integrable_sq.indicator (hA n)
  have hIw : ∀ n, Integrable (w n) P := fun n => (integrable_const (1 : ℝ)).indicator (hA n)
  have hw0 : ∀ n, 0 ≤ ∫ ω, w n ω ∂P := fun n =>
    integral_nonneg (fun ω => by
      by_cases hω : ω ∈ A n
      · simp [hwdef, Set.indicator_of_mem hω]
      · simp [hwdef, Set.indicator_of_notMem hω])
  have hs1 : ∑ n ∈ Finset.range (N + 1), ∫ ω, (A n).indicator (fun ω : AuxSpace => ω.1 ^ 2) ω ∂P = s := by
    rw [← integral_finset_sum _ (fun n _ => hIxi n)]
    have : ∀ ω, ∑ n ∈ Finset.range (N + 1), (A n).indicator (fun ω : AuxSpace => ω.1 ^ 2) ω = ω.1 ^ 2 := by
      intro ω
      have := hsum (fun _ ω => ω.1 ^ 2) ω
      simpa using this
    simp_rw [this]
    have := integral_sq_Yc s hs.le (N := 0) none
    simpa [Yc, wt] using this
  have hs2 : ∑ n ∈ Finset.range (N + 1), ∫ ω, w n ω ∂P = 1 := by
    rw [← integral_finset_sum _ (fun n _ => hIw n)]
    have : ∀ ω, ∑ n ∈ Finset.range (N + 1), w n ω = 1 := by
      intro ω
      have := hsum (fun _ _ => (1 : ℝ)) ω
      simpa [hwdef] using this
    simp_rw [this]
    simp
  have hs3 : ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ∫ ω, w n ω ∂P =
      ∫ ω, (((T ω).untopA : ℕ) : ℝ) ∂P := by
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum _ (fun n _ => (hIw n).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have := hsum (fun n _ => (n : ℝ)) ω
    simp only [hwdef]
    rw [← this]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hω : ω ∈ A n
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hmain : ∫ ω, (stoppedValue (Zproc l s) T ω) ^ 2 ∂P =
      ∑ n ∈ Finset.range (N + 1), (s - l * s / (l + n * s)) * ∫ ω, w n ω ∂P := by
    simp_rw [hZT]
    rw [integral_finset_sum _ (fun n _ => hI1 n)]
    simp_rw [hper]
    rw [Finset.sum_sub_distrib, hs1]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs2, mul_one]
  refine ⟨?_, ?_⟩
  · have : (fun ω => (stoppedValue (Zproc l s) T ω) ^ 2) =
        fun ω => ∑ n ∈ Finset.range (N + 1), (u n ω) ^ 2 := funext hZT
    rw [this]
    exact integrable_finsetSum _ (fun n _ => hI1 n)
  rw [hmain, ← hs3, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hd : 0 < l + n * s := by positivity
  have h1 : s - l * s / (l + n * s) = n * s ^ 2 / (l + n * s) := by
    field_simp; ring
  have h2 : n * s ^ 2 / (l + n * s) ≤ s ^ 2 / l * n := by
    rw [div_le_iff₀ hd]
    have : 0 ≤ (n : ℝ) * s ^ 2 := by positivity
    have e : s ^ 2 / l * n * (l + n * s) = n * s ^ 2 + (s ^ 2 / l * n * (n * s)) := by
      field_simp
    rw [e]
    have : 0 ≤ s ^ 2 / l * n * (n * s) := by positivity
    linarith
  rw [h1]
  calc n * s ^ 2 / (l + n * s) * ∫ ω, w n ω ∂P ≤ s ^ 2 / l * n * ∫ ω, w n ω ∂P :=
        mul_le_mul_of_nonneg_right h2 (hw0 n)
    _ = s ^ 2 / l * (n * ∫ ω, w n ω ∂P) := by ring


lemma Kc_mul (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M) (hs : 0 < Sig i i) :
    Kc Sig i * Sig i i = ∑ j, |Sig i j| := by
  unfold Kc
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_div, abs_of_pos hs]
  field_simp

lemma lookahead_ub (lam c : Fin M → ℝ) (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i)
    (hβ : (∑ j, |Sig i j|) / (c i * Real.sqrt (lam i)) ≤ 2)
    (T : AuxSpace → WithTop ℕ) (hT : AdmissibleLookahead (lam i) T) :
    lookaheadValue lam c mu Sig i T ≤ -1 + (∑ j, |Sig i j|) / (c i * Real.sqrt (lam i)) := by
  set P := auxMeasure (Sig i i) with hP
  set s := Sig i i with hsdef
  have h1 := lookahead_le' lam c mu Sig i hl hs hc T hT
  obtain ⟨N, hTfin, hTmeas, hTint, hT1⟩ := T_facts (lam i) s T hT
  obtain ⟨hZ2int, hZ2⟩ := EZ2 (lam i) s hl hs T hT
  set x := ∫ ω, (((T ω).untopA : ℕ) : ℝ) ∂P with hx
  obtain ⟨hst, N', hN⟩ := hT
  have hZ := stopped_eq_condExp (lam i) s hl hs hst (N := N') (fun ω => (hN ω).2)
  have hZint : Integrable (stoppedValue (Zproc (lam i) s) T) P :=
    (integrable_condExp).congr hZ.symm
  set q : ℝ := s * Real.sqrt (x / lam i) with hq
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by positivity
  have hy : ∫ ω, |stoppedValue (Zproc (lam i) s) T ω| ∂P ≤ q := by
    have hle : ∀ ω, |stoppedValue (Zproc (lam i) s) T ω| ≤
        (stoppedValue (Zproc (lam i) s) T ω) ^ 2 / (2 * q) + q / 2 := by
      intro ω
      set z := stoppedValue (Zproc (lam i) s) T ω
      rw [← sub_nonneg]
      have : z ^ 2 / (2 * q) + q / 2 - |z| = (|z| - q) ^ 2 / (2 * q) := by
        rw [← sq_abs z]; field_simp; ring
      rw [this]; positivity
    have I2' : Integrable (fun ω => (stoppedValue (Zproc (lam i) s) T ω) ^ 2 / (2 * q)) P :=
      hZ2int.div_const _
    have hint : ∫ ω, ((stoppedValue (Zproc (lam i) s) T ω) ^ 2 / (2 * q) + q / 2) ∂P =
        (∫ ω, (stoppedValue (Zproc (lam i) s) T ω) ^ 2 ∂P) / (2 * q) + q / 2 := by
      rw [integral_add I2' (integrable_const _), integral_div]
      simp
    have := (integral_mono hZint.abs (I2'.add (integrable_const (q / 2))) hle).trans hint.le
    have h3 : (∫ ω, (stoppedValue (Zproc (lam i) s) T ω) ^ 2 ∂P) / (2 * q) ≤ q / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : q ^ 2 = s ^ 2 / lam i * x := by
        rw [hq, mul_pow, Real.sq_sqrt (by positivity)]; ring
      nlinarith [hZ2, this]
    linarith
  have hK := Kc_nonneg Sig i
  have hKy : Kc Sig i / c i * ∫ ω, |stoppedValue (Zproc (lam i) s) T ω| ∂P ≤ Kc Sig i / c i * q :=
    mul_le_mul_of_nonneg_left hy (by positivity)
  set β := (∑ j, |Sig i j|) / (c i * Real.sqrt (lam i)) with hβdef
  have hKq : Kc Sig i / c i * q = β * Real.sqrt x := by
    rw [hβdef, ← Kc_mul Sig i hs, hq, Real.sqrt_div' _ hl.le]
    have : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.2 hl).ne'
    field_simp
    rfl
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hT1
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hβ0 : 0 ≤ β := by
    rw [hβdef]; positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hsx) (sub_nonneg.2 (show Real.sqrt x ≤ Real.sqrt x + 1 - β + (β - 1) by linarith))]

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

namespace CtCore

variable {M : ℕ}

lemma integral_Zproc (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (n : ℕ) :
    ∫ ω, Zproc l s n ω ∂(auxMeasure s) = 0 := by
  rw [integral_congr_ae (key l s hl hs n), integral_condExp ((auxFiltration l).le n)]
  exact integral_Yc s (N := 0) none

lemma nuCKG1_ge (lam c : Fin M → ℝ) (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i) : -1 ≤ nuCKG1 lam c mu Sig i := by
  have hZint : Integrable (Zproc (lam i) (Sig i i) 1) (auxMeasure (Sig i i)) :=
    (Zproc_martingale _ _ hl hs).integrable 1
  have hti := integrable_terminal mu Sig i hZint
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset (Fin M)).Nonempty) mu
  have hmm : maxMean mu i = mu k := hk
  have hlow : ∀ ω, mu k + Sig i k / Sig i i * Zproc (lam i) (Sig i i) 1 ω ≤
      terminal mu Sig i (Zproc (lam i) (Sig i i) 1 ω) := fun ω => by
    unfold terminal
    exact Finset.le_sup' (fun j => mu j + Sig i j / Sig i i * Zproc (lam i) (Sig i i) 1 ω)
      (Finset.mem_univ k)
  have hint := integral_mono ((integrable_const (mu k)).add (hZint.const_mul (Sig i k / Sig i i)))
    hti hlow
  have hl2 : ∫ ω, (mu k + Sig i k / Sig i i * Zproc (lam i) (Sig i i) 1 ω) ∂(auxMeasure (Sig i i))
      = mu k := by
    rw [integral_add (integrable_const _) (hZint.const_mul _), integral_const_mul,
      integral_Zproc _ _ hl hs]
    simp
  have hint : mu k ≤ ∫ ω, terminal mu Sig i (Zproc (lam i) (Sig i i) 1 ω) ∂(auxMeasure (Sig i i)) :=
    hl2.symm.le.trans hint
  unfold nuCKG1
  rw [← hmm] at hint
  have hc' : 0 < 1 / c i := by positivity
  nlinarith

lemma nuStar_ge (lam c : Fin M → ℝ) (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i) : -1 ≤ nuStar lam c mu Sig i :=
  (nuCKG1_ge lam c mu Sig i hl hs hc).trans (ec1 lam c mu Sig i hl hs hc)

lemma nuStar_le (lam c : Fin M → ℝ) (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i)
    (hβ : (∑ j, |Sig i j|) / (c i * Real.sqrt (lam i)) ≤ 2) :
    nuStar lam c mu Sig i ≤ -1 + (∑ j, |Sig i j|) / (c i * Real.sqrt (lam i)) := by
  unfold nuStar
  refine csSup_le ⟨_, ⟨fun _ => (1 : WithTop ℕ), adm_one _, rfl⟩⟩ ?_
  rintro v ⟨T, hT, rfl⟩
  exact lookahead_ub lam c mu Sig i hl hs hc hβ T hT

end CtCore

namespace CtSeq
open CtCore

variable {M : ℕ} (I : Instance M)

lemma part_b (ω : TrialSpace M) (i : Fin M)
    (h : Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0)) :
    Tendsto (fun T => nuStar I.lam I.c (mu I T ω) (Sig I T ω) i) atTop (𝓝 (-1)) := by
  set β : ℕ → ℝ := fun T => (∑ j, |Sig I T ω i j|) / (I.c i * Real.sqrt (I.lam i)) with hβ
  have hentry : ∀ j, Tendsto (fun T => |Sig I T ω i j|) atTop (𝓝 0) := by
    intro j
    have hb : Tendsto (fun T => Real.sqrt (Sig I T ω i i * I.Sig0 j j)) atTop (𝓝 0) := by
      have := (h.mul_const (I.Sig0 j j)).sqrt
      simpa using this
    refine squeeze_zero (fun T => abs_nonneg _) (fun T => ?_) hb
    apply Real.abs_le_sqrt
    calc Sig I T ω i j ^ 2 ≤ Sig I T ω i i * Sig I T ω j j := CtMat.step_cs (sig_posDef I T ω) i j
      _ ≤ Sig I T ω i i * I.Sig0 j j :=
        mul_le_mul_of_nonneg_left (sig_diag_le I T ω j) (sig_posDef I T ω).diag_pos.le
  have hβ0 : Tendsto β atTop (𝓝 0) := by
    have := (tendsto_finset_sum Finset.univ (fun j _ => hentry j)).div_const (I.c i * Real.sqrt (I.lam i))
    simpa using this
  have hev : ∀ᶠ T in atTop, β T ≤ 2 := hβ0.eventually (eventually_le_nhds (by norm_num))
  have hup : Tendsto (fun T => -1 + β T) atTop (𝓝 (-1)) := by
    simpa using (tendsto_const_nhds (x := (-1 : ℝ))).add hβ0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Eventually.of_forall fun T =>
      nuStar_ge _ _ _ _ i (I.lam_pos i) (sig_posDef I T ω).diag_pos (I.c_pos i)
  · filter_upwards [hev] with T hT
    exact nuStar_le _ _ _ _ i (I.lam_pos i) (sig_posDef I T ω).diag_pos (I.c_pos i) hT

end CtSeq

open CtSeq in
theorem solution {M : ℕ} (I : Instance M) :
    (∀ ω i, (∃ᶠ t in atTop, alloc I t ω = i) →
        Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0)) ∧
      (∀ ω i, Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) →
        Tendsto (fun T => nuStar I.lam I.c (mu I T ω) (Sig I T ω) i) atTop (𝓝 (-1))) :=
  ⟨fun ω i hi => part_a I ω i hi, fun ω i h => part_b I ω i h⟩
