-- Prove2me | solution 1 for CorrelatedTrials.Consistency.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:35:54.828401+00:00
-- url     : https://prove2.me/submissions/0a066a75-4b57-4741-8137-e24d25756381

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

lemma lookahead_le (hl : 0 < lam i) (hs : 0 < Sig i i) (hc : 0 < c i)
    (T : AuxSpace → WithTop ℕ) (hT : AdmissibleLookahead (lam i) T) :
    lookaheadValue lam c mu Sig i T ≤
      -1 + Kc Sig i / c i * ∫ ω, |ω.1| ∂(auxMeasure (Sig i i)) := by
  obtain ⟨hst, N, hN⟩ := hT
  set P := auxMeasure (Sig i i) with hP
  have hZ := stopped_eq_condExp (lam i) (Sig i i) hl hs hst (N := N) (fun ω => (hN ω).2)
  have hZint : Integrable (stoppedValue (Zproc (lam i) (Sig i i)) T) P :=
    (integrable_condExp).congr hZ.symm
  have hTfin : ∀ ω, ∃ m : ℕ, T ω = m ∧ 1 ≤ m := by
    intro ω
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hN ω).2)
    refine ⟨m, hm.symm, ?_⟩
    have := (hN ω).1
    rw [← hm] at this
    exact WithTop.coe_le_coe.1 this
  have hTmeas : Measurable (fun ω => (((T ω).untopA : ℕ) : ℝ)) := by
    have h1 : Measurable T := hst.measurable'
    exact (measurable_of_countable (fun x : WithTop ℕ => (((x.untopA : ℕ)) : ℝ))).comp h1
  have hTint : Integrable (fun ω => (((T ω).untopA : ℕ) : ℝ)) P := by
    refine Integrable.mono' (g := fun _ => (N : ℝ)) (integrable_const _) hTmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    obtain ⟨m, hm, h1⟩ := hTfin ω
    have h2 : m ≤ N := by
      have := (hN ω).2
      rw [hm] at this
      exact_mod_cast this
    simp only [hm, WithTop.untopD_coe, Real.norm_eq_abs, Nat.abs_cast]
    exact_mod_cast h2
  have hf : Integrable (fun ω => -(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal mu Sig i (stoppedValue (Zproc (lam i) (Sig i i)) T ω)) P :=
    hTint.neg.add ((integrable_terminal mu Sig i hZint).const_mul _)
  have hg : Integrable (fun ω => -1 + (1 / c i) * (maxMean mu i + Kc Sig i *
      |stoppedValue (Zproc (lam i) (Sig i i)) T ω|)) P :=
    (integrable_const _).add (((integrable_const _).add (hZint.abs.const_mul _)).const_mul _)
  have hle : ∀ ω, -(((T ω).untopA : ℕ) : ℝ) +
      (1 / c i) * terminal mu Sig i (stoppedValue (Zproc (lam i) (Sig i i)) T ω) ≤
      -1 + (1 / c i) * (maxMean mu i + Kc Sig i *
        |stoppedValue (Zproc (lam i) (Sig i i)) T ω|) := by
    intro ω
    obtain ⟨m, hm, h1⟩ := hTfin ω
    have h1' : (1 : ℝ) ≤ (((T ω).untopA : ℕ) : ℝ) := by
      simp only [hm, WithTop.untopD_coe]; exact_mod_cast h1
    have := terminal_le mu Sig i (stoppedValue (Zproc (lam i) (Sig i i)) T ω)
    have hc' : 0 < 1 / c i := by positivity
    nlinarith
  have hint := integral_mono hf hg hle
  have habs : ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P ≤ ∫ ω, |ω.1| ∂P := by
    calc ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P
        = ∫ ω, |P[fun ω : AuxSpace => ω.1 | hst.measurableSpace] ω| ∂P :=
          integral_congr_ae (hZ.mono fun ω h => by dsimp only; rw [h])
      _ ≤ ∫ ω, |ω.1| ∂P := integral_abs_condExp_le _
  have i1 : ∫ ω, (1 / c i) * (maxMean mu i + Kc Sig i *
      |stoppedValue (Zproc (lam i) (Sig i i)) T ω|) ∂P =
      (1 / c i) * (maxMean mu i + Kc Sig i *
        ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P) := by
    rw [integral_const_mul, integral_add (integrable_const _) (hZint.abs.const_mul _),
      integral_const_mul]
    simp
  have hg_int : ∫ ω, (-1 + (1 / c i) * (maxMean mu i + Kc Sig i *
      |stoppedValue (Zproc (lam i) (Sig i i)) T ω|)) ∂P =
      -1 + (1 / c i) * (maxMean mu i + Kc Sig i *
        ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P) := by
    rw [integral_add (f := fun _ : AuxSpace => (-1 : ℝ))
      (g := fun ω => (1 / c i) * (maxMean mu i + Kc Sig i *
      |stoppedValue (Zproc (lam i) (Sig i i)) T ω|)) (integrable_const _)
      (((integrable_const _).add (hZint.abs.const_mul _)).const_mul _), i1]
    simp
  unfold lookaheadValue
  rw [hg_int] at hint
  have hK := Kc_nonneg Sig i
  have hc' : 0 < 1 / c i := by positivity
  have : Kc Sig i / c i * ∫ ω, |ω.1| ∂P ≥ Kc Sig i / c i * ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  have e : 1 / c i * (maxMean mu i + Kc Sig i *
        ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P) - 1 / c i * maxMean mu i =
      Kc Sig i / c i * ∫ ω, |stoppedValue (Zproc (lam i) (Sig i i)) T ω| ∂P := by ring
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

open CtCore in
theorem solution {M : ℕ} (lam c : Fin M → ℝ) (mu : Fin M → ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (hSig : Sig.PosDef) (hlam : ∀ j, 0 < lam j) (hc : ∀ j, 0 < c j) :
    nuCKG1 lam c mu Sig i ≤ nuStar lam c mu Sig i :=
  ec1 lam c mu Sig i (hlam i) (hSig.diag_pos (i := i)) (hc i)
