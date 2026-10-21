-- Prove2me | solution 1 for CorrelatedTrials.Consistency.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:32:12.455138+00:00
-- url     : https://prove2.me/submissions/d5b9b74f-a0ca-4079-8da5-a1bce991874e

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_AllocationIndex

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

lemma optional_stopping (l s : ℝ) (hl : 0 < l) (hs : 0 < s) (T : AuxSpace → WithTop ℕ)
    (hT : IsStoppingTime (auxFiltration l) T) (hfin : ∀ᵐ ω ∂(auxMeasure s), T ω ≠ ⊤) :
    ∫ ω, stoppedValue (Zproc l s) T ω ∂(auxMeasure s) = 0 := by
  set P := auxMeasure s
  have hTn : ∀ n : ℕ, IsStoppingTime (auxFiltration l) (fun ω => min (T ω) (n : WithTop ℕ)) :=
    fun n => hT.min_const n
  have hW : ∀ n : ℕ, stoppedValue (Zproc l s) (fun ω => min (T ω) (n : WithTop ℕ)) =ᵐ[P]
      P[fun ω : AuxSpace => ω.1 | (hTn n).measurableSpace] := fun n =>
    stopped_eq_condExp l s hl hs (hTn n) (fun ω => min_le_right _ _)
  have hUI : UniformIntegrable
      (fun n : ℕ => stoppedValue (Zproc l s) (fun ω => min (T ω) (n : WithTop ℕ))) 1 P :=
    ((integrable_xi s).uniformIntegrable_condExp
      (ℱ := fun n : ℕ => (hTn n).measurableSpace)
      (fun n => ((hTn n).measurableSpace_le_of_le_const (i := n) (fun ω => min_le_right _ _)).trans
        ((auxFiltration l).le n))).ae_eq (fun n => (hW n).symm)
  have htend : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => stoppedValue (Zproc l s) (fun ω => min (T ω) (n : WithTop ℕ)) ω) atTop
      (𝓝 (stoppedValue (Zproc l s) T ω)) := by
    filter_upwards [hfin] with ω hω
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hω
    refine tendsto_atTop_of_eventually_const (i₀ := m) (fun n hn => ?_)
    have : min (T ω) (n : WithTop ℕ) = T ω := by
      rw [← hm]; exact min_eq_left (WithTop.coe_le_coe.mpr hn)
    simp only [stoppedValue, this]
  have hg : MemLp (stoppedValue (Zproc l s) T) 1 P := hUI.memLp_of_ae_tendsto htend
  have hL := tendsto_Lp_finite_of_tendsto_ae (le_refl 1) ENNReal.one_ne_top hUI.1 hg hUI.2.1 htend
  have hI := tendsto_integral_of_L1' (stoppedValue (Zproc l s) T) hg.1
    (Eventually.of_forall fun n => (hUI.memLp n).integrable le_rfl) hL
  have h0 : ∀ n : ℕ, ∫ ω, stoppedValue (Zproc l s) (fun ω => min (T ω) (n : WithTop ℕ)) ω ∂P = 0 := by
    intro n
    rw [integral_congr_ae (hW n),
      integral_condExp ((hTn n).measurableSpace_le_of_le_const (i := n) (fun ω => min_le_right _ _)
        |>.trans ((auxFiltration l).le n))]
    exact integral_Yc s (N := 0) none
  simp only [h0] at hI
  exact (tendsto_nhds_unique tendsto_const_nhds hI).symm

end CtCore

open CtCore in
theorem solution {M : ℕ} (lam : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (hlam : 0 < lam i) (hSig : 0 < Sig i i) :
    Martingale (Zproc (lam i) (Sig i i)) (auxFiltration (lam i)) (auxMeasure (Sig i i)) ∧
      UniformIntegrable (Zproc (lam i) (Sig i i)) 1 (auxMeasure (Sig i i)) ∧
      ∀ T : AuxSpace → WithTop ℕ, IsStoppingTime (auxFiltration (lam i)) T →
        (∀ᵐ ω ∂(auxMeasure (Sig i i)), T ω ≠ ⊤) →
        ∫ ω, stoppedValue (Zproc (lam i) (Sig i i)) T ω ∂(auxMeasure (Sig i i)) = 0 :=
  ⟨Zproc_martingale _ _ hlam hSig, Zproc_ui _ _ hlam hSig,
    fun T hT hfin => optional_stopping _ _ hlam hSig T hT hfin⟩
