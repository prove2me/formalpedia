-- Prove2me | solution 1 for BurkholderDFI.Gundy.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T03:50:46.533892+00:00
-- url     : https://prove2.me/submissions/5df3c9a4-bd0e-429d-b8cd-f5a625309681

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- BEGIN COMPLETE MODULE ExitEvents
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*}

def goodEvent (f : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k, 1≤k → k≤n → |f k ω|≤l}

def exitEvent (f : ℕ → Ω → ℝ) (l : ℝ) (k : ℕ) : Set Ω :=
  goodEvent f l (k-1) \ goodEvent f l k

noncomputable def exitStop (f : ℕ → Ω → ℝ) (l : ℝ) : Ω → WithTop ℕ :=
  hittingAfter f {x | l < |x|} 1

@[simp] lemma goodEvent_zero (f : ℕ → Ω → ℝ) (l : ℝ) : goodEvent f l 0=univ := by
  ext ω
  simp only [goodEvent,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  intro k hk hk0
  omega

lemma goodEvent_antitone (f : ℕ → Ω → ℝ) (l : ℝ) : Antitone (goodEvent f l) := by
  intro m n h ω hω k hk hkm
  exact hω k hk (hkm.trans h)

lemma goodEvent_succ (f : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) :
    goodEvent f l (n+1) = goodEvent f l n ∩ {ω | |f (n+1) ω|≤l} := by
  ext ω
  constructor
  · intro h
    exact ⟨goodEvent_antitone f l (Nat.le_succ n) h,h (n+1) (by omega) le_rfl⟩
  · rintro ⟨h,hn⟩ k hk hkn
    by_cases he : k=n+1
    · simpa [he] using hn
    · exact h k hk (by omega)

lemma exitStop_gt_iff (f : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) (ω : Ω) :
    (n : WithTop ℕ)<exitStop f l ω ↔ ω∈goodEvent f l n := by
  have he := hittingAfter_le_iff (u := f) (s := {x : ℝ | l < |x|}) (n := 1) (i := n) (ω := ω)
  simp only [ENat.some_eq_natCast] at he
  rw [←not_le,exitStop,he]
  simp only [Set.mem_Icc,Set.mem_ofPred_eq,goodEvent,not_exists,not_and,not_lt]
  constructor
  · intro h k hk hkn
    exact h k ⟨hk,hkn⟩
  · intro h k hk
    exact h k hk.1 hk.2

lemma exitStop_one_le (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) :
    (1 : WithTop ℕ)≤exitStop f l ω := le_hittingAfter ω

variable [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma measurableSet_goodEvent (hf : StronglyAdapted ℱ f) (l : ℝ) (n : ℕ) :
    MeasurableSet[ℱ n] (goodEvent f l n) := by
  change MeasurableSet[ℱ n] {ω | ∀ k, 1≤k → k≤n → |f k ω|≤l}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun hkn => by
      have hm : @Measurable Ω ℝ (ℱ n) _ (f k) :=
        (hf k).measurable.mono (ℱ.mono hkn) le_rfl
      exact measurableSet_le (mδ := ℱ n)
        (@Measurable.abs ℝ Ω _ _ _ (ℱ n) (f k) _ _ hm) measurable_const

lemma exitStop_isStoppingTime (hf : StronglyAdapted ℱ f) (l : ℝ) :
    IsStoppingTime ℱ (exitStop f l) := by
  change IsStoppingTime ℱ (hittingAfter f {x | l < |x|} 1)
  apply hf.adapted.isStoppingTime_hittingAfter
  exact measurableSet_lt measurable_const measurable_id.abs

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE ExitEvents

-- BEGIN COMPLETE MODULE TruncatedIncrements
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*}

noncomputable def beforeInc (f : ℕ → Ω → ℝ) (l : ℝ) (k : ℕ) : Ω → ℝ :=
  (goodEvent f l k).indicator (dseq f k)

noncomputable def exitInc (f : ℕ → Ω → ℝ) (l : ℝ) (k : ℕ) : Ω → ℝ :=
  (exitEvent f l k).indicator (dseq f k)

lemma beforeInc_bound (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0≤l) (k : ℕ) (ω : Ω) :
    |beforeInc f l k ω|≤2*l := by
  classical
  by_cases hg : ω∈goodEvent f l k
  · rw [beforeInc,Set.indicator_of_mem hg]
    by_cases hk : k=0
    · simp [dseq,hk,hl]
    by_cases hk1 : k=1
    · have hh := hg 1 le_rfl (by omega)
      simpa [dseq,hk1] using hh.trans (by linarith : l≤2*l)
    · have h1 := hg k (by omega) le_rfl
      have h2 := hg (k-1) (by omega) (by omega)
      simp only [dseq,if_neg hk,if_neg hk1]
      exact (abs_sub _ _).trans (by linarith)
  · rw [beforeInc,Set.indicator_of_notMem hg,abs_zero]
    positivity

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma stronglyAdapted_dseq (hf : StronglyAdapted ℱ f) : StronglyAdapted ℱ (dseq f) := by
  intro k
  by_cases hk : k=0
  · subst k
    change @StronglyMeasurable Ω ℝ _ (ℱ 0) (fun _ : Ω => (0 : ℝ))
    exact stronglyMeasurable_const
  by_cases hk1 : k=1
  · subst k
    change @StronglyMeasurable Ω ℝ _ (ℱ 1) (f 1)
    exact hf 1
  · have he : dseq f k = f k - f (k-1) := by
      funext ω
      simp [dseq,hk,hk1]
    rw [he]
    exact (hf k).sub ((hf (k-1)).mono (ℱ.mono (Nat.sub_le _ _)))

omit [IsProbabilityMeasure P] in
lemma stronglyAdapted_beforeInc (hf : StronglyAdapted ℱ f) (l : ℝ) :
    StronglyAdapted ℱ (beforeInc f l) := by
  intro k
  exact (stronglyAdapted_dseq hf k).indicator (measurableSet_goodEvent hf l k)

lemma beforeInc_memLp (hf : StronglyAdapted ℱ f) {l : ℝ} (hl : 0≤l) (k : ℕ)
    (p : ℝ≥0∞) : MemLp (beforeInc f l k) p P := by
  apply MemLp.of_bound (((stronglyAdapted_beforeInc hf l k).mono (ℱ.le k)).aestronglyMeasurable) (2*l)
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using beforeInc_bound f hl k ω

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE TruncatedIncrements

-- BEGIN COMPLETE MODULE EnergyAlgebra
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*}

noncomputable def previousValue (f : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  if n=0 then 0 else f n

lemma dseq_succ_eq (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    dseq f (n+1) ω = f (n+1) ω - previousValue f n ω := by
  by_cases hn : n=0
  · subst n; simp [dseq,previousValue]
  · simp [dseq,previousValue,hn]

lemma energy_local_identity (f : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) (ω : Ω) :
    (beforeInc f l (n+1) ω)^2 +
      2 * previousValue f n ω * (goodEvent f l n).indicator (dseq f (n+1)) ω =
      (goodEvent f l (n+1)).indicator (fun ω => (f (n+1) ω)^2) ω -
      (goodEvent f l n).indicator (fun ω => (previousValue f n ω)^2) ω +
      (exitEvent f l (n+1)).indicator
        (fun ω => 2*previousValue f n ω*f (n+1) ω-(previousValue f n ω)^2) ω := by
  classical
  have hd := dseq_succ_eq f n ω
  by_cases hn : ω∈goodEvent f l n
  · by_cases hs : ω∈goodEvent f l (n+1)
    · have he : ω∉exitEvent f l (n+1) := by simp [exitEvent,hs]
      simp only [beforeInc,Set.indicator_of_mem hs,Set.indicator_of_mem hn,
        Set.indicator_of_notMem he,hd]
      ring
    · have he : ω∈exitEvent f l (n+1) := by simpa [exitEvent] using And.intro hn hs
      simp only [beforeInc,Set.indicator_of_notMem hs,Set.indicator_of_mem hn,
        Set.indicator_of_mem he,hd]
      ring
  · have hs : ω∉goodEvent f l (n+1) := fun hs => hn (goodEvent_antitone f l (by omega) hs)
    have he : ω∉exitEvent f l (n+1) := by simpa [exitEvent] using fun h : ω∈goodEvent f l n ∧ ω∉goodEvent f l (n+1) => hn h.1
    simp only [beforeInc,Set.indicator_of_notMem hs,Set.indicator_of_notMem hn,
      Set.indicator_of_notMem he]
    ring

lemma energy_telescope (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    (∑ k∈Finset.range N, (beforeInc f l (k+1) ω)^2) +
      (∑ k∈Finset.range N, 2*previousValue f k ω *
        (goodEvent f l k).indicator (dseq f (k+1)) ω) =
    (goodEvent f l N).indicator (fun ω => (previousValue f N ω)^2) ω +
      ∑ k∈Finset.range N, (exitEvent f l (k+1)).indicator
        (fun ω => 2*previousValue f k ω*f (k+1) ω-(previousValue f k ω)^2) ω := by
  classical
  induction N with
  | zero => simp [previousValue]
  | succ N ih =>
    have hv : previousValue f (N+1) = f (N+1) := by simp [previousValue]
    simp only [Finset.sum_range_succ,hv]
    have hh := energy_local_identity f l N ω
    linarith

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE EnergyAlgebra

-- BEGIN COMPLETE MODULE PredictableCancellation
section

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {m : MeasurableSpace Ω}

lemma integral_mul_zero_of_condExp_zero (hm : m ≤ mΩ) {g f : Ω → ℝ}
    (hg : StronglyMeasurable[m] g) (hf : Integrable f P)
    (hgf : Integrable (fun ω=>g ω*f ω) P) (hz : P[f|m]=ᵐ[P] 0) :
    (∫ω,g ω*f ω ∂P)=0 := by
  calc
    _ = ∫ω,P[g*f|m] ω ∂P := (integral_condExp hm).symm
    _ = ∫ω,g ω*P[f|m] ω ∂P := integral_congr_ae
      (condExp_mul_of_stronglyMeasurable_left hg hgf hf)
    _ = 0 := by
      calc
        _ = ∫ω,(0:ℝ) ∂P := integral_congr_ae (by filter_upwards [hz] with ω hω; simp [hω])
        _ = 0 := integral_zero _ _

lemma integral_predictable_martingale_difference {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (n : ℕ) {g : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ n] g)
    (hgf : Integrable (fun ω=>g ω*(f (n+1) ω-f n ω)) P) :
    (∫ω,g ω*(f (n+1) ω-f n ω) ∂P)=0 := by
  apply integral_mul_zero_of_condExp_zero (mΩ:=mΩ) (ℱ.le n) hg
    ((hf.integrable _).sub (hf.integrable _)) hgf
  refine (condExp_sub (hf.integrable (n+1)) (hf.integrable n) (ℱ n)).trans ?_
  rw [condExp_of_stronglyMeasurable (ℱ.le n) (hf.stronglyAdapted n) (hf.integrable n)]
  filter_upwards [hf.2 n (n+1) (Nat.le_succ n)] with ω hω
  simp only [Pi.sub_apply,hω,sub_self,Pi.zero_apply]

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE PredictableCancellation

-- BEGIN COMPLETE MODULE EnergyCross
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*}

noncomputable def predictableValue (f : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) : Ω → ℝ :=
  (goodEvent f l n).indicator (previousValue f n)

lemma predictableValue_bound (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0≤l) (n : ℕ) (ω : Ω) :
    |predictableValue f l n ω|≤l := by
  classical
  by_cases hn : n=0
  · subst n; simpa [predictableValue,previousValue] using hl
  by_cases hg : ω∈goodEvent f l n
  · simpa [predictableValue,Set.indicator_of_mem hg,previousValue,hn] using hg n (by omega) le_rfl
  · simpa [predictableValue,Set.indicator_of_notMem hg] using hl

lemma cross_eq (f : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) (ω : Ω) :
    2*previousValue f n ω*(goodEvent f l n).indicator (dseq f (n+1)) ω =
      2*(predictableValue f l n ω*dseq f (n+1) ω) := by
  classical
  by_cases hg : ω∈goodEvent f l n <;> simp [predictableValue,hg,mul_assoc]

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma predictableValue_measurable (hf : StronglyAdapted ℱ f) (l : ℝ) (n : ℕ) :
    StronglyMeasurable[ℱ n] (predictableValue f l n) := by
  apply StronglyMeasurable.indicator _ (measurableSet_goodEvent hf l n)
  by_cases hn : n=0
  · simp only [previousValue,if_pos hn]; exact stronglyMeasurable_const
  · simpa only [previousValue,if_neg hn] using hf n

omit [IsProbabilityMeasure P] in
lemma integrable_dseq (hf : Martingale f ℱ P) (k : ℕ) : Integrable (dseq f k) P := by
  by_cases hk : k=0
  · subst k; exact integrable_zero _ _ _
  by_cases hk1 : k=1
  · subst k; exact hf.integrable 1
  have he : dseq f k=f k - f (k-1) := by funext ω; simp [dseq,hk,hk1]
  rw [he]
  exact (hf.integrable _).sub (hf.integrable _)

omit [IsProbabilityMeasure P] in
lemma cross_integrable (hf : Martingale f ℱ P) {l : ℝ} (hl : 0≤l) (n : ℕ) :
    Integrable (fun ω=>2*previousValue f n ω*(goodEvent f l n).indicator (dseq f (n+1)) ω) P := by
  simp_rw [cross_eq]
  apply Integrable.const_mul _ 2
  exact (integrable_dseq hf _).bdd_mul
    ((predictableValue_measurable hf.stronglyAdapted l n).mono (ℱ.le n)).aestronglyMeasurable
    (ae_of_all _ fun ω=>by simpa only [Real.norm_eq_abs] using predictableValue_bound f hl n ω)

lemma cross_integral_zero (hf : Martingale f ℱ P) {l : ℝ} (hl : 0≤l) (n : ℕ) :
    (∫ω,2*previousValue f n ω*(goodEvent f l n).indicator (dseq f (n+1)) ω ∂P)=0 := by
  by_cases hn : n=0
  · subst n; simp [previousValue]
  have he : dseq f (n+1)= f (n+1) - f n := by
    funext ω; simp [dseq,hn]
  simp_rw [cross_eq,he,Pi.sub_apply]
  rw [integral_const_mul]
  have hi := (integrable_dseq hf (n+1)).bdd_mul
    ((predictableValue_measurable hf.stronglyAdapted l n).mono (ℱ.le n)).aestronglyMeasurable
    (ae_of_all _ fun ω=>by simpa only [Real.norm_eq_abs] using predictableValue_bound f hl n ω)
  rw [he] at hi
  rw [integral_predictable_martingale_difference hf n
    (predictableValue_measurable hf.stronglyAdapted l n) hi,mul_zero]

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE EnergyCross

-- BEGIN COMPLETE MODULE EnergyUpper
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*}

lemma previous_abs_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0≤l) (n : ℕ) (ω : Ω)
    (hg : ω∈goodEvent f l n) : |previousValue f n ω|≤l := by
  by_cases hn : n=0
  · simp [previousValue,hn,hl]
  · simpa [previousValue,hn] using hg n (by omega) le_rfl

lemma terminal_energy_bound (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0≤l) (N : ℕ) (ω : Ω) :
    (goodEvent f l N).indicator (fun ω=>(previousValue f N ω)^2) ω ≤
      2*l*(goodEvent f l N).indicator (fun ω=>|f N ω|) ω := by
  classical
  by_cases hg : ω∈goodEvent f l N
  · simp only [Set.indicator_of_mem hg]
    by_cases hn : N=0
    · simp only [previousValue,if_pos hn,Pi.zero_apply,zero_pow (by norm_num : 2≠0)]
      positivity
    · have hb := previous_abs_le f hl N ω hg
      simp only [previousValue,if_neg hn] at hb ⊢
      nlinarith [sq_abs (f N ω),abs_nonneg (f N ω),mul_nonneg hl (abs_nonneg (f N ω))]
  · simp only [Set.indicator_of_notMem hg,mul_zero,le_refl]

lemma exit_energy_bound (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0≤l) (k : ℕ) (ω : Ω) :
    (exitEvent f l (k+1)).indicator
      (fun ω=>2*previousValue f k ω*f (k+1) ω-(previousValue f k ω)^2) ω ≤
      2*l*(exitEvent f l (k+1)).indicator (fun ω=>|f (k+1) ω|) ω := by
  classical
  by_cases he : ω∈exitEvent f l (k+1)
  · simp only [Set.indicator_of_mem he]
    have hg : ω∈goodEvent f l k := by simpa [exitEvent] using he.1
    have hb := previous_abs_le f hl k ω hg
    have hm : previousValue f k ω*f (k+1) ω ≤ l*|f (k+1) ω| := by
      calc
        _ ≤ |previousValue f k ω*f (k+1) ω| := le_abs_self _
        _ = |previousValue f k ω| * |f (k+1) ω| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    nlinarith [sq_nonneg (previousValue f k ω)]
  · simp only [Set.indicator_of_notMem he,mul_zero,le_refl]

lemma energy_pointwise_bound (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0≤l) (N : ℕ) (ω : Ω) :
    (∑ k∈Finset.range N,(beforeInc f l (k+1) ω)^2)+
      (∑ k∈Finset.range N,2*previousValue f k ω*
        (goodEvent f l k).indicator (BurkholderDFI.SquareFnLp.dseq f (k+1)) ω) ≤
    2*l*((goodEvent f l N).indicator (fun ω=>|f N ω|) ω+
      ∑ k∈Finset.range N,(exitEvent f l (k+1)).indicator (fun ω=>|f (k+1) ω|) ω) := by
  rw [energy_telescope,mul_add,Finset.mul_sum]
  exact add_le_add (terminal_energy_bound f hl N ω)
    (Finset.sum_le_sum fun k _=>exit_energy_bound f hl k ω)

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE EnergyUpper

-- BEGIN COMPLETE MODULE StoppedMartingale
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma martingale_stopped (hf : Martingale f ℱ P) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) : Martingale (stoppedProcess f τ) ℱ P := by
  apply martingale_iff.mpr
  have hn := (hf.neg.submartingale.stoppedProcess hτ).neg
  have he : -(stoppedProcess (-f) τ) = stoppedProcess f τ := by
    funext n ω
    simp only [Pi.neg_apply,stoppedProcess,neg_neg]
  rw [he] at hn
  exact ⟨hn,hf.submartingale.stoppedProcess hτ⟩

omit [IsProbabilityMeasure P] in
lemma abs_submartingale (hf : Martingale f ℱ P) :
    Submartingale (fun n ω => |f n ω|) ℱ P := by
  have hh := hf.submartingale.sup hf.neg.submartingale
  have he : f ⊔ -f = fun n ω => |f n ω| := by
    funext n ω
    exact abs_eq_max_neg.symm
  rw [he] at hh
  exact hh

lemma stopped_abs_integral_le (hf : Martingale f ℱ P) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    (∫ ω, |stoppedProcess f τ n ω| ∂P) ≤ ∫ ω, |f n ω| ∂P := by
  have hh := (abs_submartingale hf).expected_stoppedValue_mono
    ((isStoppingTime_const ℱ n).min hτ) (isStoppingTime_const ℱ n)
    (fun ω => min_le_left _ _) (fun _ => le_rfl)
  simpa [stoppedProcess,stoppedValue,←ENat.some_eq_natCast] using hh

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE StoppedMartingale

-- BEGIN COMPLETE MODULE NativeL1Bound
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma lpNormE_one (g : Ω → ℝ≥0∞) : lpNormE P 1 g = ∫⁻ ω,g ω ∂P := by
  simp [lpNormE]

omit [IsProbabilityMeasure P] in
lemma integral_abs_le_pNorm (hf : Martingale f ℱ P) (hfin : pNorm P 1 f < ⊤)
    {n : ℕ} (hn : 1≤n) : (∫ ω,|f n ω| ∂P) ≤ (pNorm P 1 f).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp
  rw [ofReal_integral_eq_lintegral_ofReal (hf.integrable n).abs (ae_of_all _ (fun _=>abs_nonneg _))]
  rw [←lpNormE_one]
  exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

lemma stopped_abs_le_pNorm (hf : Martingale f ℱ P) (hfin : pNorm P 1 f < ⊤)
    (l : ℝ) {n : ℕ} (hn : 1≤n) :
    (∫ ω,|stoppedProcess f (exitStop f l) n ω| ∂P) ≤ (pNorm P 1 f).toReal :=
  (stopped_abs_integral_le hf (exitStop_isStoppingTime hf.stronglyAdapted l) n).trans
    (integral_abs_le_pNorm hf hfin hn)

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE NativeL1Bound

-- BEGIN COMPLETE MODULE CenteredBasic
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℕ mΩ}

noncomputable def centeredIncrement (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (a : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  if k=0 then a 1 else a (k+1)-P[a (k+1)|ℱ k]

noncomputable def centeredProcess (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (a : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  if n=0 then P[a 1|ℱ 0] else ∑ k∈Finset.range n,centeredIncrement ℱ P a k

lemma centeredIncrement_zero (a : ℕ → Ω → ℝ) : centeredIncrement ℱ P a 0=a 1 := by
  simp [centeredIncrement]

lemma centeredIncrement_succ (a : ℕ → Ω → ℝ) (k : ℕ) :
    centeredIncrement ℱ P a (k+1)=a (k+2)-P[a (k+2)|ℱ (k+1)] := by
  simp [centeredIncrement,Nat.add_assoc]

lemma centeredProcess_zero (a : ℕ → Ω → ℝ) : centeredProcess ℱ P a 0=P[a 1|ℱ 0] := by
  simp [centeredProcess]

lemma centeredProcess_pos (a : ℕ → Ω → ℝ) {n : ℕ} (hn : 0<n) :
    centeredProcess ℱ P a n=∑ k∈Finset.range n,centeredIncrement ℱ P a k := by
  simp [centeredProcess,hn.ne']

lemma centeredProcess_one (a : ℕ → Ω → ℝ) : centeredProcess ℱ P a 1=a 1 := by
  simp [centeredProcess,centeredIncrement]

lemma centeredProcess_succ (a : ℕ → Ω → ℝ) {n : ℕ} (hn : 0<n) :
    centeredProcess ℱ P a (n+1)=centeredProcess ℱ P a n+centeredIncrement ℱ P a n := by
  rw [centeredProcess_pos a (by omega),centeredProcess_pos a hn,Finset.sum_range_succ]

lemma centeredIncrement_integrable {a : ℕ → Ω → ℝ}
    (ha : ∀k,Integrable (a k) P) (k : ℕ) : Integrable (centeredIncrement ℱ P a k) P := by
  by_cases hk : k=0
  · simp only [centeredIncrement,if_pos hk]; exact ha 1
  · simp only [centeredIncrement,if_neg hk]; exact (ha _).sub integrable_condExp

lemma centeredProcess_integrable {a : ℕ → Ω → ℝ}
    (ha : ∀k,Integrable (a k) P) (n : ℕ) : Integrable (centeredProcess ℱ P a n) P := by
  by_cases hn : n=0
  · simp only [centeredProcess,if_pos hn]; exact integrable_condExp
  · rw [centeredProcess_pos a (Nat.pos_of_ne_zero hn)]
    exact integrable_finsetSum' (Finset.range n)
      (fun k _=>centeredIncrement_integrable (ℱ:=ℱ) ha k)

lemma centeredIncrement_adapted {a : ℕ → Ω → ℝ} (ha : StronglyAdapted ℱ a) (k : ℕ) :
    StronglyMeasurable[ℱ (k+1)] (centeredIncrement ℱ P a k) := by
  by_cases hk : k=0
  · subst k; rw [centeredIncrement_zero]; exact ha 1
  · simp only [centeredIncrement,if_neg hk]
    exact (ha _).sub (stronglyMeasurable_condExp.mono (ℱ.mono k.le_succ))

lemma centeredProcess_adapted {a : ℕ → Ω → ℝ} (ha : StronglyAdapted ℱ a) :
    StronglyAdapted ℱ (centeredProcess ℱ P a) := by
  intro n
  by_cases hn : n=0
  · subst n; rw [centeredProcess_zero]; exact stronglyMeasurable_condExp
  · rw [centeredProcess_pos a (Nat.pos_of_ne_zero hn)]
    exact Finset.stronglyMeasurable_sum _ fun k hk=>
      (centeredIncrement_adapted ha k).mono (ℱ.mono (by simpa using Finset.mem_range.mp hk))

variable [IsFiniteMeasure P]

lemma centeredIncrement_condExp_zero {a : ℕ → Ω → ℝ}
    (ha : ∀k,Integrable (a k) P) {k : ℕ} (hk : 0<k) :
    P[centeredIncrement ℱ P a k|ℱ k]=ᵐ[P] 0 := by
  rw [centeredIncrement,if_neg hk.ne']
  refine (condExp_sub (ha _) integrable_condExp _).trans ?_
  rw [condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp]
  exact Filter.Eventually.of_forall fun _=>sub_self _

lemma martingale_centeredProcess {a : ℕ → Ω → ℝ} (ha : StronglyAdapted ℱ a)
    (hi : ∀k,Integrable (a k) P) : Martingale (centeredProcess ℱ P a) ℱ P := by
  apply martingale_nat (centeredProcess_adapted ha) (centeredProcess_integrable hi)
  intro n
  by_cases hn : n=0
  · subst n; rw [centeredProcess_zero,centeredProcess_one]
  · rw [centeredProcess_succ a (Nat.pos_of_ne_zero hn)]
    refine ((condExp_add (centeredProcess_integrable hi n)
      (centeredIncrement_integrable hi n) _).trans ?_).symm
    rw [condExp_of_stronglyMeasurable (ℱ.le n) (centeredProcess_adapted ha n)
      (centeredProcess_integrable hi n)]
    filter_upwards [centeredIncrement_condExp_zero (ℱ:=ℱ) hi (Nat.pos_of_ne_zero hn)] with ω hω
    simp only [Pi.add_apply,hω,Pi.zero_apply,add_zero]

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE CenteredBasic

-- BEGIN COMPLETE MODULE CenteredL2
section

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {m : MeasurableSpace Ω}

lemma integral_square_add {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ω,(f ω+g ω)^2 ∂P) = (∫ω,f ω^2 ∂P)+2*(∫ω,f ω*g ω ∂P)+(∫ω,g ω^2 ∂P) := by
  have hm : Integrable (fun ω=>f ω*g ω) P := hf.integrable_mul hg
  have hleft : Integrable (fun ω=>f ω^2+2*(f ω*g ω)) P :=
    hf.integrable_sq.add (hm.const_mul 2)
  calc
    _ = ∫ω,(f ω^2+2*(f ω*g ω))+g ω^2 ∂P := by congr 1; funext ω; ring
    _ = _ := by
      rw [integral_add hleft hg.integrable_sq,
        integral_add hf.integrable_sq (hm.const_mul 2),integral_const_mul]

variable [IsFiniteMeasure P]

lemma integral_mul_condExp_eq (hm : m ≤ mΩ) {g f : Ω → ℝ}
    (hg : StronglyMeasurable[m] g) (hg2 : MemLp g 2 P) (hf2 : MemLp f 2 P) :
    (∫ω,g ω*f ω ∂P) = ∫ω,g ω*P[f|m] ω ∂P := by
  calc
    _ = ∫ω,P[g*f|m] ω ∂P := (integral_condExp hm).symm
    _ = _ := integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg
      (hg2.integrable_mul hf2) (hf2.integrable (by norm_num)))

lemma integral_mul_centered_zero (hm : m ≤ mΩ) {g f : Ω → ℝ}
    (hg : StronglyMeasurable[m] g) (hg2 : MemLp g 2 P) (hf2 : MemLp f 2 P) :
    (∫ω,g ω*(f ω-P[f|m] ω) ∂P)=0 := by
  have hc2 : MemLp (P[f|m]) 2 P := hf2.condExp (by norm_num)
  have h1 : Integrable (fun ω=>g ω*f ω) P := hg2.integrable_mul hf2
  have h2 : Integrable (fun ω=>g ω*P[f|m] ω) P := hg2.integrable_mul hc2
  simp_rw [mul_sub]
  rw [integral_sub h1 h2,
    integral_mul_condExp_eq (mΩ:=mΩ) (P:=P) hm hg hg2 hf2,sub_self]

lemma centered_square_le (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ω,(f ω-P[f|m] ω)^2 ∂P) ≤ ∫ω,f ω^2 ∂P := by
  have hc : MemLp (P[f|m]) 2 P := hf.condExp (by norm_num)
  have hr := hf.sub hc
  have hz := integral_mul_centered_zero (mΩ:=mΩ) (P:=P) hm stronglyMeasurable_condExp hc hf
  have he := integral_square_add (mΩ:=mΩ) hc hr
  simp only [Pi.sub_apply] at he
  simp_rw [show ∀ω,P[f|m] ω+(f ω-P[f|m] ω)=f ω by intro ω; ring] at he
  rw [hz] at he
  have hn : 0≤∫ω,P[f|m] ω^2 ∂P := integral_nonneg fun _=>sq_nonneg _
  linarith

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE CenteredL2

-- BEGIN COMPLETE MODULE CenteredEnergy
section

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

omit [IsFiniteMeasure P] in
lemma centeredIncrement_memLp {a : ℕ → Ω → ℝ} (ha : ∀k,MemLp (a k) 2 P) (k : ℕ) :
    MemLp (centeredIncrement ℱ P a k) 2 P := by
  by_cases hk : k=0
  · subst k; rw [centeredIncrement_zero]; exact ha 1
  · rw [centeredIncrement,if_neg hk]
    exact (ha _).sub ((ha _).condExp (by norm_num))

omit [IsFiniteMeasure P] in
lemma centeredProcess_memLp {a : ℕ → Ω → ℝ} (ha : ∀k,MemLp (a k) 2 P) (n : ℕ) :
    MemLp (centeredProcess ℱ P a n) 2 P := by
  by_cases hn : n=0
  · subst n; rw [centeredProcess_zero]; exact (ha 1).condExp (by norm_num)
  · rw [centeredProcess_pos a (Nat.pos_of_ne_zero hn)]
    exact memLp_finsetSum' _ (fun k _=>centeredIncrement_memLp (ℱ:=ℱ) ha k)

lemma centeredProcess_energy {a : ℕ → Ω → ℝ} (ha : StronglyAdapted ℱ a)
    (h2 : ∀k,MemLp (a k) 2 P) {N : ℕ} (hN : 0<N) :
    (∫ω,centeredProcess ℱ P a N ω^2 ∂P) ≤
      ∑k∈Finset.range N, ∫ω,a (k+1) ω^2 ∂P := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  induction n with
  | zero => simp [centeredProcess_one]
  | succ n ih =>
    have ih := ih (by omega)
    have hx := centeredProcess_memLp (ℱ:=ℱ) h2 (n+1)
    have hd := centeredIncrement_memLp (ℱ:=ℱ) h2 (n+1)
    have hz := integral_mul_centered_zero (ℱ.le (n+1))
      (centeredProcess_adapted ha (n+1)) hx (h2 (n+2))
    have he := integral_square_add hx hd
    rw [centeredIncrement_succ] at he
    change (∫ω,(centeredProcess ℱ P a (n+1) ω+
      (a (n+2) ω-P[a (n+2)|ℱ (n+1)] ω))^2 ∂P)=_ at he
    simp only [Pi.sub_apply] at he
    rw [hz] at he
    have hvar := centered_square_le (ℱ.le (n+1)) (h2 (n+2))
    rw [centeredProcess_succ a (by omega),Finset.sum_range_succ]
    simp only [Pi.add_apply,centeredIncrement_succ,Pi.sub_apply]
    linarith

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE CenteredEnergy

-- BEGIN COMPLETE MODULE NativeL2Norm
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma lpNormE_two_sq {f : Ω → ℝ} (hf : MemLp f 2 P) :
    lpNormE P 2 (fun ω=>ENNReal.ofReal |f ω|) ^ (2:ℝ)=
      ENNReal.ofReal (∫ω,f ω^2 ∂P) := by
  rw [lpNormE,←ENNReal.rpow_mul]
  norm_num only [one_div_mul_cancel (by norm_num : (2:ℝ)≠0),ENNReal.rpow_one]
  simp only [ENNReal.rpow_two,←ENNReal.ofReal_pow (abs_nonneg _),sq_abs]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Filter.Eventually.of_forall fun _=>sq_nonneg _)).symm

lemma pNorm_two_sq_le {X : ℕ → Ω → ℝ} {C : ℝ}
    (h2 : ∀n,1≤n → MemLp (X n) 2 P)
    (hC : ∀n,1≤n → (∫ω,X n ω^2 ∂P)≤C) :
    pNorm P 2 X ^ (2:ℝ)≤ENNReal.ofReal C := by
  have hb : pNorm P 2 X≤ENNReal.ofReal C ^ (1/2:ℝ) := by
    apply iSup_le
    intro n
    apply iSup_le
    intro hn
    have hh := ENNReal.ofReal_le_ofReal (hC n hn)
    rw [←lpNormE_two_sq (h2 n hn)] at hh
    have ht := ENNReal.rpow_le_rpow hh (by norm_num : (0:ℝ)≤1/2)
    simpa only [←ENNReal.rpow_mul,mul_one_div_cancel (by norm_num : (2:ℝ)≠0),
      ENNReal.rpow_one] using ht
  have ht := ENNReal.rpow_le_rpow hb (by norm_num : (0:ℝ)≤2)
  simpa only [←ENNReal.rpow_mul,one_div_mul_cancel (by norm_num : (2:ℝ)≠0),
    ENNReal.rpow_one] using ht

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE NativeL2Norm

-- BEGIN COMPLETE MODULE EnergyIntegral
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma before_energy_integral (hf : Martingale f ℱ P) {l : ℝ} (hl : 0≤l) (N : ℕ)
    (hpath : ∀ω,(goodEvent f l N).indicator (fun ω=>|f N ω|) ω+
      ∑ k∈Finset.range N,(exitEvent f l (k+1)).indicator (fun ω=>|f (k+1) ω|) ω =
      |stoppedProcess f (exitStop f l) N ω|) :
    (∑ k∈Finset.range N,∫ω,(beforeInc f l (k+1) ω)^2 ∂P) ≤
      2*l*(∫ω,|stoppedProcess f (exitStop f l) N ω| ∂P) := by
  have ha k : Integrable (fun ω=>(beforeInc f l (k+1) ω)^2) P :=
    (beforeInc_memLp hf.stronglyAdapted hl (k+1) 2).integrable_sq
  have hc k := cross_integrable hf hl k
  have hS := (martingale_stopped hf (exitStop_isStoppingTime hf.stronglyAdapted l)).integrable N
  have hh := integral_mono ((integrable_finsetSum (Finset.range N) (fun k _=>ha k)).add
      (integrable_finsetSum (Finset.range N) (fun k _=>hc k))) (hS.abs.const_mul (2*l))
      (fun ω=>by simpa only [Finset.sum_apply,Pi.add_apply,hpath ω] using energy_pointwise_bound f hl N ω)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_finsetSum (Finset.range N) (fun k _=>ha k))
    (integrable_finsetSum (Finset.range N) (fun k _=>hc k)),integral_finsetSum _ (fun k _=>ha k),
    integral_finsetSum _ (fun k _=>hc k),integral_const_mul] at hh
  simp only [cross_integral_zero hf hl,Finset.sum_const_zero,add_zero] at hh
  exact hh

lemma good_process_energy (hf : Martingale f ℱ P) (hL1 : pNorm P 1 f<⊤)
    {l : ℝ} (hl : 0≤l) {N : ℕ} (hN : 0<N)
    (hpath : ∀ω,(goodEvent f l N).indicator (fun ω=>|f N ω|) ω+
      ∑ k∈Finset.range N,(exitEvent f l (k+1)).indicator (fun ω=>|f (k+1) ω|) ω =
      |stoppedProcess f (exitStop f l) N ω|) :
    (∫ω,centeredProcess ℱ P (beforeInc f l) N ω^2 ∂P)≤
      2*l*(pNorm P 1 f).toReal := by
  exact (centeredProcess_energy (stronglyAdapted_beforeInc hf.stronglyAdapted l)
    (fun k=>beforeInc_memLp hf.stronglyAdapted hl k 2) hN).trans
    ((before_energy_integral hf hl N hpath).trans
      (mul_le_mul_of_nonneg_left (stopped_abs_le_pNorm hf hL1 l hN) (by positivity)))

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE EnergyIntegral

-- BEGIN COMPLETE MODULE ExitIdentities
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*}

lemma exitEvent_eq_stop (f : ℕ → Ω → ℝ) (l : ℝ) {k : ℕ} (hk : 1≤k) (ω : Ω) :
    ω∈exitEvent f l k ↔ exitStop f l ω=(k : WithTop ℕ) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  simp only [exitEvent,Nat.succ_sub_one,Set.mem_sdiff,←exitStop_gt_iff,not_lt]
  constructor
  · rintro ⟨h1,h2⟩
    apply le_antisymm h2
    rcases eq_or_ne (exitStop f l ω) ⊤ with ht | ht
    · simp [ht]
    · lift exitStop f l ω to ℕ using ht with r hr
      exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp h1))
  · intro h
    rw [h]
    exact ⟨by exact_mod_cast Nat.lt_succ_self j,le_rfl⟩

lemma exit_event_abs_gt (f : ℕ → Ω → ℝ) (l : ℝ) {k : ℕ} (hk : 1≤k)
    {ω : Ω} (he : ω∈exitEvent f l k) : l < |f k ω| := by
  by_contra hh
  apply he.2
  intro j hj hjk
  by_cases hj' : j=k
  · simpa [hj'] using le_of_not_gt hh
  · exact he.1 j hj (by omega)

lemma stopped_at_exit (f : ℕ → Ω → ℝ) (l : ℝ) {k n : ℕ} (hk : 1≤k) (hkn : k≤n)
    {ω : Ω} (he : ω∈exitEvent f l k) : stoppedProcess f (exitStop f l) n ω=f k ω := by
  have ht := (exitEvent_eq_stop f l hk ω).mp he
  rw [stoppedProcess_eq_of_ge (u := f) (i := n) (show exitStop f l ω ≤ (n : WithTop ℕ) by rw [ht]; exact WithTop.coe_le_coe.mpr hkn), ht]
  rfl

lemma exitEvent_disjoint (f : ℕ → Ω → ℝ) (l : ℝ) {j k : ℕ}
    (hj : 1≤j) (hk : 1≤k) (hne : j≠k) : Disjoint (exitEvent f l j) (exitEvent f l k) := by
  apply Set.disjoint_left.mpr
  intro ω h1 h2
  have he := ((exitEvent_eq_stop f l hj ω).mp h1).symm.trans
    ((exitEvent_eq_stop f l hk ω).mp h2)
  exact hne (by exact_mod_cast he)

lemma exit_dseq_bound (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0≤l) {k : ℕ} (hk : 1≤k)
    {ω : Ω} (he : ω∈exitEvent f l k) : |dseq f k ω|≤|f k ω|+l := by
  by_cases hk1 : k=1
  · simp only [dseq,if_neg (by omega : k≠0),if_pos hk1]
    simp only [hk1]
    linarith
  · simp only [dseq,if_neg (by omega : k≠0),if_neg hk1]
    exact (abs_sub _ _).trans (add_le_add_right (he.1 (k-1) (by omega) le_rfl) _)

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE ExitIdentities

-- BEGIN COMPLETE MODULE ExitFinite
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*}

lemma not_good_iff_exists_exit (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    ω ∉ goodEvent f l N ↔ ∃ k ∈ Finset.range N, ω ∈ exitEvent f l (k+1) := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    constructor
    · intro h
      by_cases hg : ω ∈ goodEvent f l N
      · exact ⟨N,Finset.mem_range.mpr (Nat.lt_succ_self _), by simpa [exitEvent] using And.intro hg h⟩
      · obtain ⟨k,hk,he⟩ := ih.mp hg
        exact ⟨k,Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans (Nat.lt_succ_self _)),he⟩
    · rintro ⟨k,hk,he⟩ hg
      exact he.2 (goodEvent_antitone f l (by simpa using Finset.mem_range.mp hk) hg)

lemma exit_sum_single (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω)
    (v : ℕ → Ω → ℝ) {k : ℕ} (hk : k ∈ Finset.range N)
    (he : ω ∈ exitEvent f l (k+1)) :
    (∑ j ∈ Finset.range N, (exitEvent f l (j+1)).indicator (v (j+1)) ω) = v (k+1) ω := by
  classical
  rw [Finset.sum_eq_single k]
  · exact Set.indicator_of_mem he _
  · intro j _ hj
    apply Set.indicator_of_notMem
    intro hj'
    exact Set.disjoint_left.mp (exitEvent_disjoint f l (by omega) (by omega) (by omega : j+1≠k+1)) hj' he
  · exact fun hn => (hn hk).elim

lemma stopped_abs_decomposition (f : ℕ → Ω → ℝ) (l : ℝ) {N : ℕ} (_hN : 1 ≤ N) (ω : Ω) :
    |stoppedProcess f (exitStop f l) N ω| =
      (goodEvent f l N).indicator (fun ω => |f N ω|) ω +
      ∑ k ∈ Finset.range N, (exitEvent f l (k+1)).indicator (fun ω => |f (k+1) ω|) ω := by
  classical
  by_cases hg : ω ∈ goodEvent f l N
  · rw [Set.indicator_of_mem hg, stoppedProcess_eq_of_le (u := f) (i := N) ((exitStop_gt_iff f l N ω).mpr hg).le]
    have hz : ∀ k ∈ Finset.range N, (exitEvent f l (k+1)).indicator (fun ω => |f (k+1) ω|) ω = 0 := by
      intro k hk
      apply Set.indicator_of_notMem
      intro he
      exact he.2 (goodEvent_antitone f l (Finset.mem_range.mp hk) hg)
    simp only [Finset.sum_eq_zero hz,add_zero]
  · obtain ⟨k,hk,he⟩ := (not_good_iff_exists_exit f l N ω).mp hg
    rw [Set.indicator_of_notMem hg,zero_add,exit_sum_single f l N ω (fun j ω => |f j ω|) hk he]
    rw [stopped_at_exit f l (by omega) (Finset.mem_range.mp hk) he]

lemma exit_sum_bound (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 ≤ l) (N : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range N, |exitInc f l (k+1) ω|) ≤
      |stoppedProcess f (exitStop f l) N ω| + l * (goodEvent f l N)ᶜ.indicator (fun _ => (1:ℝ)) ω := by
  classical
  have hid (j : ℕ) : |exitInc f l j ω| = (exitEvent f l j).indicator (fun ω => |dseq f j ω|) ω := by
    by_cases he : ω ∈ exitEvent f l j <;> simp [exitInc,he]
  simp_rw [hid]
  by_cases hg : ω ∈ goodEvent f l N
  · have hz : ∀ k ∈ Finset.range N, (exitEvent f l (k+1)).indicator (fun ω => |dseq f (k+1) ω|) ω = 0 := by
      intro k hk
      apply Set.indicator_of_notMem
      intro he
      exact he.2 (goodEvent_antitone f l (Finset.mem_range.mp hk) hg)
    rw [Finset.sum_eq_zero hz, Set.indicator_of_notMem (show ω ∉ (goodEvent f l N)ᶜ from fun h => h hg), mul_zero, add_zero]
    exact abs_nonneg _
  · obtain ⟨k,hk,he⟩ := (not_good_iff_exists_exit f l N ω).mp hg
    rw [exit_sum_single f l N ω (fun j ω => |dseq f j ω|) hk he,
      Set.indicator_of_mem (show ω ∈ (goodEvent f l N)ᶜ from hg),mul_one,
      stopped_at_exit f l (by omega) (Finset.mem_range.mp hk) he]
    exact exit_dseq_bound f hl (by omega) he

lemma bad_stopped_abs_gt (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) {ω : Ω}
    (hg : ω ∉ goodEvent f l N) : l < |stoppedProcess f (exitStop f l) N ω| := by
  obtain ⟨k,hk,he⟩ := (not_good_iff_exists_exit f l N ω).mp hg
  rw [stopped_at_exit f l (by omega) (Finset.mem_range.mp hk) he]
  exact exit_event_abs_gt f l (by omega) he

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE ExitFinite

-- BEGIN COMPLETE MODULE GoodProcessBound
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma good_process_pNorm (hf : Martingale f ℱ P) (hL1 : pNorm P 1 f<⊤)
    {l : ℝ} (hl : 0≤l) :
    pNorm P 2 (centeredProcess ℱ P (beforeInc f l)) ^ (2:ℝ) ≤
      ENNReal.ofReal (2*l)*pNorm P 1 f := by
  have hh := pNorm_two_sq_le
    (fun n _=>centeredProcess_memLp (ℱ:=ℱ) (fun k=>beforeInc_memLp hf.stronglyAdapted hl k 2) n)
    (fun n hn=>good_process_energy hf hL1 hl hn
      (fun ω=>(stopped_abs_decomposition f l hn ω).symm))
  rw [ENNReal.ofReal_mul (by positivity : 0≤2*l),ENNReal.ofReal_toReal hL1.ne] at hh
  exact hh

lemma martingale_good_process (hf : Martingale f ℱ P) {l : ℝ} (hl : 0≤l) :
    Martingale (centeredProcess ℱ P (beforeInc f l)) ℱ P :=
  martingale_centeredProcess (stronglyAdapted_beforeInc hf.stronglyAdapted l)
    (fun k=>(beforeInc_memLp hf.stronglyAdapted hl k 1).integrable (by norm_num))

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE GoodProcessBound

-- BEGIN COMPLETE MODULE CenteredVariation
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BurkholderDFI.Gundy.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℕ mΩ}

lemma centeredProcess_difference (a : ℕ → Ω → ℝ) (k : ℕ) :
    BurkholderDFI.SquareFnLp.dseq (centeredProcess ℱ P a) (k+1)=centeredIncrement ℱ P a k := by
  funext ω
  cases k with
  | zero => simp [BurkholderDFI.SquareFnLp.dseq,centeredProcess_one,centeredIncrement_zero]
  | succ k =>
    simp only [BurkholderDFI.SquareFnLp.dseq,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    rw [if_neg (by omega),centeredProcess_succ a (by omega)]
    simp

lemma centeredIncrement_abs_bound {a : ℕ → Ω → ℝ}
    (hi : ∀k,Integrable (a k) P) (k : ℕ) :
    (∫ω,|centeredIncrement ℱ P a k ω| ∂P) ≤ 2*(∫ω,|a (k+1) ω| ∂P) := by
  by_cases hk : k=0
  · subst k; rw [centeredIncrement_zero]
    have : 0≤∫ω,|a 1 ω| ∂P := integral_nonneg fun _=>abs_nonneg _
    simp only [zero_add]; linarith
  · rw [centeredIncrement,if_neg hk]
    have hh : (∫ω,|a (k+1) ω-P[a (k+1)|ℱ k] ω| ∂P) ≤
        (∫ω,|a (k+1) ω| ∂P)+(∫ω,|P[a (k+1)|ℱ k] ω| ∂P) := by
      rw [←integral_add (hi _).abs integrable_condExp.abs]
      apply integral_mono ((hi _).sub integrable_condExp).abs
        ((hi _).abs.add integrable_condExp.abs)
      intro ω
      exact abs_sub _ _
    have hb := integral_abs_condExp_le (μ:=P) (m:=ℱ k) (a (k+1))
    change (∫ω,|a (k+1) ω-P[a (k+1)|ℱ k] ω| ∂P)≤_
    linarith

lemma centeredIncrement_lintegral_bound {a : ℕ → Ω → ℝ}
    (hi : ∀k,Integrable (a k) P) (k : ℕ) :
    (∫⁻ω,ENNReal.ofReal |centeredIncrement ℱ P a k ω| ∂P) ≤
      2*(∫⁻ω,ENNReal.ofReal |a (k+1) ω| ∂P) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (centeredIncrement_integrable (ℱ:=ℱ) hi k).abs
    (Filter.Eventually.of_forall fun _=>abs_nonneg _),
    ←ofReal_integral_eq_lintegral_ofReal (hi _).abs
    (Filter.Eventually.of_forall fun _=>abs_nonneg _)]
  have hh := ENNReal.ofReal_le_ofReal (centeredIncrement_abs_bound (ℱ:=ℱ) hi k)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat] using hh

lemma centeredProcess_variation {a : ℕ → Ω → ℝ}
    (hi : ∀k,Integrable (a k) P) :
    (∫⁻ω,∑'k:ℕ,ENNReal.ofReal |BurkholderDFI.SquareFnLp.dseq
      (centeredProcess ℱ P a) (k+1) ω| ∂P) ≤
      2*(∫⁻ω,∑'k:ℕ,ENNReal.ofReal |a (k+1) ω| ∂P) := by
  simp_rw [centeredProcess_difference]
  rw [lintegral_tsum (fun k=>(centeredIncrement_integrable (ℱ:=ℱ) hi k).abs.aemeasurable.ennreal_ofReal),
    lintegral_tsum (fun k=>(hi (k+1)).abs.aemeasurable.ennreal_ofReal),←ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (centeredIncrement_lintegral_bound (ℱ:=ℱ) hi)

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE CenteredVariation

-- BEGIN COMPLETE MODULE CenteredReconstruction
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ}

omit [IsProbabilityMeasure P] in
lemma centeredIncrement_add_ae {a b : ℕ → Ω → ℝ}
    (ha : ∀k,Integrable (a k) P) (hb : ∀k,Integrable (b k) P) (k : ℕ) :
    centeredIncrement ℱ P (a+b) k =ᵐ[P]
      centeredIncrement ℱ P a k+centeredIncrement ℱ P b k := by
  by_cases hk : k=0
  · subst k; simp only [centeredIncrement_zero,Pi.add_apply]; rfl
  · simp only [centeredIncrement,if_neg hk,Pi.add_apply]
    filter_upwards [condExp_add (ha (k+1)) (hb (k+1)) (ℱ k)] with ω hω
    simp only [Pi.add_apply,Pi.sub_apply] at hω ⊢
    rw [hω]
    ring

omit [IsProbabilityMeasure P] in
lemma centeredProcess_add_ae {a b : ℕ → Ω → ℝ}
    (ha : ∀k,Integrable (a k) P) (hb : ∀k,Integrable (b k) P) {n : ℕ} (hn : 0<n) :
    centeredProcess ℱ P (a+b) n =ᵐ[P]
      centeredProcess ℱ P a n+centeredProcess ℱ P b n := by
  rw [centeredProcess_pos _ hn,centeredProcess_pos _ hn,centeredProcess_pos _ hn]
  have hh : ∀ᵐω ∂P,∀k,centeredIncrement ℱ P (a+b) k ω=
      (centeredIncrement ℱ P a k+centeredIncrement ℱ P b k) ω :=
    ae_all_iff.mpr (fun k=>centeredIncrement_add_ae ha hb k)
  filter_upwards [hh] with ω hω
  simp only [Finset.sum_apply,Pi.add_apply]
  simp_rw [hω,Pi.add_apply]
  exact Finset.sum_add_distrib

lemma martingale_centered_dseq {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    {n : ℕ} (hn : 0<n) : centeredProcess ℱ P (dseq f) n =ᵐ[P] f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n; rw [centeredProcess_one]; rfl
    have hp : 0<n := Nat.pos_of_ne_zero hn0
    rw [centeredProcess_succ _ hp,centeredIncrement,if_neg hn0]
    have hd : dseq f (n+1)=f (n+1)-f n := by funext ω; simp [dseq,hn0]
    rw [hd]
    have hz : P[f (n+1)-f n|ℱ n]=ᵐ[P] 0 := by
      refine (condExp_sub (hf.integrable _) (hf.integrable _) _).trans ?_
      rw [condExp_of_stronglyMeasurable (ℱ.le n) (hf.stronglyAdapted n) (hf.integrable n)]
      filter_upwards [hf.2 n (n+1) (Nat.le_succ n)] with ω hω
      simp only [Pi.sub_apply,hω,sub_self,Pi.zero_apply]
    filter_upwards [ih hp,hz] with ω hω hzω
    simp only [Pi.add_apply,Pi.sub_apply,hω,hzω,Pi.zero_apply]
    ring

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE CenteredReconstruction

-- BEGIN COMPLETE MODULE VariationCongruence
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma dseq_congr_ae_positive {Y V : ℕ → Ω → ℝ}
    (h : ∀n,1≤n→Y n=ᵐ[P]V n) (k : ℕ) : dseq Y (k+1)=ᵐ[P]dseq V (k+1) := by
  cases k with
  | zero => exact h 1 le_rfl
  | succ k =>
    filter_upwards [h (k+1+1) (by omega),h (k+1) (by omega)] with ω h1 h2
    simp only [dseq,if_neg (by omega : k+1+1≠0),if_neg (by omega : k+1+1≠1),
      Nat.add_sub_cancel,h1,h2]

lemma variation_congr_ae_positive {Y V : ℕ → Ω → ℝ}
    (h : ∀n,1≤n→Y n=ᵐ[P]V n) :
    (∫⁻ω,∑'k:ℕ,ENNReal.ofReal |dseq Y (k+1) ω| ∂P)=
      ∫⁻ω,∑'k:ℕ,ENNReal.ofReal |dseq V (k+1) ω| ∂P := by
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun k=>dseq_congr_ae_positive h k)] with ω hω
  exact tsum_congr fun k=>by rw [hω k]

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE VariationCongruence

-- BEGIN COMPLETE MODULE CenteredSplit
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ}

omit [IsProbabilityMeasure P] in
lemma centeredProcess_congr_positive {a b : ℕ → Ω → ℝ}
    (h : ∀k,1≤k→a k=b k) {n : ℕ} (hn : 0<n) :
    centeredProcess ℱ P a n=centeredProcess ℱ P b n := by
  rw [centeredProcess_pos _ hn,centeredProcess_pos _ hn]
  apply Finset.sum_congr rfl
  intro k _
  unfold centeredIncrement
  rw [h 1 le_rfl,h (k+1) (by omega)]

lemma stopped_minus_centered_ae {S a b : ℕ → Ω → ℝ}
    (hS : Martingale S ℱ P) (ha : ∀k,Integrable (a k) P) (hb : ∀k,Integrable (b k) P)
    (hsplit : ∀k,1≤k→dseq S k=a k+b k) {n : ℕ} (hn : 0<n) :
    (S-centeredProcess ℱ P a) n =ᵐ[P] centeredProcess ℱ P b n := by
  have he : centeredProcess ℱ P (a+b) n=centeredProcess ℱ P (dseq S) n :=
    centeredProcess_congr_positive (fun k hk=>(hsplit k hk).symm) hn
  have hh := centeredProcess_add_ae (ℱ:=ℱ) ha hb hn
  rw [he] at hh
  filter_upwards [hh,martingale_centered_dseq hS hn] with ω hω hsω
  simp only [Pi.add_apply] at hω
  simp only [Pi.sub_apply]
  linarith

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE CenteredSplit

-- BEGIN COMPLETE MODULE StoppedIncrementSplit
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*}

lemma stop_succ_eq_of_good (f : ℕ → Ω → ℝ) (l : ℝ) (j : ℕ) {ω : Ω}
    (hg : ω ∈ goodEvent f l j) : stoppedProcess f (exitStop f l) (j+1) ω=f (j+1) ω := by
  apply stoppedProcess_eq_of_le (u := f) (i := j+1)
  have ht := (exitStop_gt_iff f l j ω).mpr hg
  rcases eq_or_ne (exitStop f l ω) ⊤ with he | he
  · simp [he]
  · lift exitStop f l ω to ℕ using he with r hr
    exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp ht))

lemma stopped_increment_split (f : ℕ → Ω → ℝ) (l : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    dseq (stoppedProcess f (exitStop f l)) k = beforeInc f l k + exitInc f l k := by
  classical
  funext ω
  have part : beforeInc f l k ω + exitInc f l k ω =
      (goodEvent f l (k-1)).indicator (dseq f k) ω := by
    by_cases hg : ω ∈ goodEvent f l k
    · have hp := goodEvent_antitone f l (Nat.sub_le k 1) hg
      have he : ω ∉ exitEvent f l k := fun h => h.2 hg
      simp [beforeInc,exitInc,hg,hp,he]
    · by_cases hp : ω ∈ goodEvent f l (k-1)
      · have he : ω ∈ exitEvent f l k := ⟨hp,hg⟩
        simp [beforeInc,exitInc,hg,hp,he]
      · have he : ω ∉ exitEvent f l k := fun h => hp h.1
        simp [beforeInc,exitInc,hg,hp,he]
  change dseq (stoppedProcess f (exitStop f l)) k ω = beforeInc f l k ω + exitInc f l k ω
  rw [part]
  by_cases hk1 : k=1
  · subst k
    simpa [dseq] using stoppedProcess_eq_of_le (u := f) (i := 1) (exitStop_one_le f l ω)
  have hk0 : k≠0 := by omega
  simp only [dseq,if_neg hk0,if_neg hk1]
  by_cases hg : ω ∈ goodEvent f l (k-1)
  · rw [Set.indicator_of_mem hg,
      stoppedProcess_eq_of_le (u := f) (i := k-1) ((exitStop_gt_iff f l (k-1) ω).mpr hg).le]
    have hs := stop_succ_eq_of_good f l (k-1) hg
    simpa only [Nat.sub_add_cancel hk,dseq,if_neg hk0,if_neg hk1] using congrArg (fun z => z-f (k-1) ω) hs
  · rw [Set.indicator_of_notMem hg]
    have ht : exitStop f l ω ≤ ((k-1 : ℕ) : WithTop ℕ) := le_of_not_gt (fun h => hg ((exitStop_gt_iff f l (k-1) ω).mp h))
    rw [stoppedProcess_eq_of_ge (u := f) (i := k) (ht.trans (WithTop.coe_le_coe.mpr (Nat.sub_le k 1))),
      stoppedProcess_eq_of_ge (u := f) (i := k-1) ht,sub_self]

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE StoppedIncrementSplit

-- BEGIN COMPLETE MODULE ExitMeasurable
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma measurableSet_exitEvent (hf : StronglyAdapted ℱ f) (l : ℝ) (k : ℕ) :
    MeasurableSet[ℱ k] (exitEvent f l k) :=
  (ℱ.mono (Nat.sub_le k 1) _ (measurableSet_goodEvent hf l (k-1))).diff
    (measurableSet_goodEvent hf l k)

lemma stronglyAdapted_exitInc (hf : StronglyAdapted ℱ f) (l : ℝ) :
    StronglyAdapted ℱ (exitInc f l) := by
  intro k
  exact (stronglyAdapted_dseq hf k).indicator (measurableSet_exitEvent hf l k)

lemma exitInc_integrable (hf : Martingale f ℱ P) (l : ℝ) (k : ℕ) :
    Integrable (exitInc f l k) P := by
  have hi : Integrable (dseq f k) P := by
    by_cases hk : k=0
    · subst k
      change Integrable (fun _ : Ω => (0 : ℝ)) P
      exact integrable_zero Ω ℝ P
    by_cases hk1 : k=1
    · subst k
      exact hf.integrable 1
    · have he : dseq f k = f k - f (k-1) := by funext ω; simp [dseq,hk,hk1]
      rw [he]
      exact (hf.integrable k).sub (hf.integrable (k-1))
  exact hi.indicator (ℱ.le k _ (measurableSet_exitEvent hf.stronglyAdapted l k))

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE ExitMeasurable

-- BEGIN COMPLETE MODULE ExitEstimates
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma stopped_lintegral_le_pNorm (hf : Martingale f ℱ P) (l : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal |stoppedProcess f (exitStop f l) N ω| ∂P) ≤ pNorm P 1 f := by
  have hs := (martingale_stopped hf (exitStop_isStoppingTime hf.stronglyAdapted l)).integrable N
  rw [←ofReal_integral_eq_lintegral_ofReal hs.abs (ae_of_all _ (fun _ => abs_nonneg _))]
  apply (ENNReal.ofReal_le_ofReal (stopped_abs_integral_le hf (exitStop_isStoppingTime hf.stronglyAdapted l) N)).trans
  rw [ofReal_integral_eq_lintegral_ofReal (hf.integrable N).abs (ae_of_all _ (fun _ => abs_nonneg _)),←lpNormE_one]
  exact le_iSup_of_le N (le_iSup_of_le hN le_rfl)

lemma finite_exit_probability_mul (hf : Martingale f ℱ P) {l : ℝ} (_hl : 0 ≤ l) (N : ℕ) :
    ENNReal.ofReal l * P (goodEvent f l N)ᶜ ≤ pNorm P 1 f := by
  by_cases hN : N=0
  · simp [hN]
  have hm : MeasurableSet (goodEvent f l N)ᶜ :=
    (ℱ.le N _ (measurableSet_goodEvent hf.stronglyAdapted l N)).compl
  have hpoint : ∀ ω, (goodEvent f l N)ᶜ.indicator (fun _ => ENNReal.ofReal l) ω ≤
      ENNReal.ofReal |stoppedProcess f (exitStop f l) N ω| := by
    intro ω
    by_cases hg : ω ∈ goodEvent f l N
    · simp only [Set.indicator_of_notMem (show ω ∉ (goodEvent f l N)ᶜ from fun h => h hg)]
      exact bot_le
    · rw [Set.indicator_of_mem (show ω ∈ (goodEvent f l N)ᶜ from hg)]
      exact ENNReal.ofReal_le_ofReal (bad_stopped_abs_gt f l N hg).le
  calc
    ENNReal.ofReal l * P (goodEvent f l N)ᶜ = ∫⁻ ω, (goodEvent f l N)ᶜ.indicator (fun _ => ENNReal.ofReal l) ω ∂P := by
      rw [lintegral_indicator_const hm]
    _ ≤ ∫⁻ ω, ENNReal.ofReal |stoppedProcess f (exitStop f l) N ω| ∂P := lintegral_mono hpoint
    _ ≤ pNorm P 1 f := stopped_lintegral_le_pNorm hf l (by omega)

lemma finite_exit_lintegral (hf : Martingale f ℱ P) {l : ℝ} (hl : 0 ≤ l) (N : ℕ) :
    (∫⁻ ω, ∑ k ∈ Finset.range N, ENNReal.ofReal |exitInc f l (k+1) ω| ∂P) ≤ 2*pNorm P 1 f := by
  classical
  by_cases hN : N=0
  · simp [hN]
  have hm : MeasurableSet (goodEvent f l N)ᶜ :=
    (ℱ.le N _ (measurableSet_goodEvent hf.stronglyAdapted l N)).compl
  have hs := (martingale_stopped hf (exitStop_isStoppingTime hf.stronglyAdapted l)).integrable N
  have hi : Measurable ((goodEvent f l N)ᶜ.indicator (fun _ : Ω => ENNReal.ofReal l)) := measurable_const.indicator hm
  have hpoint : ∀ ω, (∑ k ∈ Finset.range N, ENNReal.ofReal |exitInc f l (k+1) ω|) ≤
      ENNReal.ofReal |stoppedProcess f (exitStop f l) N ω| + (goodEvent f l N)ᶜ.indicator (fun _ => ENNReal.ofReal l) ω := by
    intro ω
    rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
    have he := ENNReal.ofReal_le_ofReal (exit_sum_bound f hl N ω)
    have hind : ENNReal.ofReal (l * (goodEvent f l N)ᶜ.indicator (fun _ => (1:ℝ)) ω) =
        (goodEvent f l N)ᶜ.indicator (fun _ => ENNReal.ofReal l) ω := by
      by_cases hg : ω ∈ (goodEvent f l N)ᶜ <;> simp [hg]
    have hn : 0 ≤ l * (goodEvent f l N)ᶜ.indicator (fun _ => (1:ℝ)) ω := by
      apply mul_nonneg hl
      by_cases hg : ω ∈ (goodEvent f l N)ᶜ <;> simp [hg]
    rw [ENNReal.ofReal_add (abs_nonneg _) hn,hind] at he
    exact he
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal |stoppedProcess f (exitStop f l) N ω| + (goodEvent f l N)ᶜ.indicator (fun _ => ENNReal.ofReal l) ω ∂P := lintegral_mono hpoint
    _ = (∫⁻ ω, ENNReal.ofReal |stoppedProcess f (exitStop f l) N ω| ∂P) + ENNReal.ofReal l * P (goodEvent f l N)ᶜ := by
      rw [lintegral_add_right _ hi,lintegral_indicator_const hm]
    _ ≤ pNorm P 1 f + pNorm P 1 f := add_le_add (stopped_lintegral_le_pNorm hf l (by omega)) (finite_exit_probability_mul hf hl N)
    _ = 2*pNorm P 1 f := (two_mul _).symm

lemma exit_lintegral_bound (hf : Martingale f ℱ P) {l : ℝ} (hl : 0 ≤ l) :
    (∫⁻ ω, ∑' k : ℕ, ENNReal.ofReal |exitInc f l (k+1) ω| ∂P) ≤ 2*pNorm P 1 f := by
  have hm (k : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal |exitInc f l (k+1) ω|) P :=
    (exitInc_integrable hf l (k+1)).aestronglyMeasurable.aemeasurable.abs.ennreal_ofReal
  rw [lintegral_tsum hm]
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [←lintegral_finsetSum' _ (fun k _ => hm k)]
  exact finite_exit_lintegral hf hl N

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE ExitEstimates

-- BEGIN COMPLETE MODULE BadProcessBound
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma bad_process_variation (hf : Martingale f ℱ P) {l : ℝ} (hl : 0≤l) :
    (∫⁻ω,∑'k:ℕ,ENNReal.ofReal |dseq
      (stoppedProcess f (exitStop f l)-centeredProcess ℱ P (beforeInc f l)) (k+1) ω| ∂P) ≤
      4*pNorm P 1 f := by
  have he n (hn : 1≤n) := stopped_minus_centered_ae
    (martingale_stopped hf (exitStop_isStoppingTime hf.stronglyAdapted l))
    (fun k=>(beforeInc_memLp hf.stronglyAdapted hl k 1).integrable (by norm_num))
    (exitInc_integrable hf l) (fun k hk=>stopped_increment_split f l hk) hn
  rw [variation_congr_ae_positive he]
  calc
    _ ≤ 2*(∫⁻ω,∑'k:ℕ,ENNReal.ofReal |exitInc f l (k+1) ω| ∂P) :=
      centeredProcess_variation (ℱ:=ℱ) (exitInc_integrable hf l)
    _ ≤ 2*(2*pNorm P 1 f) := mul_le_mul' le_rfl (exit_lintegral_bound hf hl)
    _ = 4*pNorm P 1 f := by ring

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE BadProcessBound

-- BEGIN COMPLETE MODULE RemainderSupport
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*}

lemma remainder_support (f : ℕ → Ω → ℝ) (l : ℝ) :
    {ω|0 < maxFn (f-stoppedProcess f (exitStop f l)) ω}⊆
      {ω|exitStop f l ω≠⊤} := by
  intro ω hω ht
  have hz : ∀n,(f-stoppedProcess f (exitStop f l)) n ω=0 := by
    intro n
    simp [Pi.sub_apply,stoppedProcess,ht,-ENat.some_eq_natCast]
  have hm : maxFn (f-stoppedProcess f (exitStop f l)) ω=0 := by
    simp [maxFn,maxFnN,hz]
  change 0 < maxFn (f-stoppedProcess f (exitStop f l)) ω at hω
  rw [hm] at hω
  exact (lt_irrefl (0:ℝ≥0∞)) hω

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE RemainderSupport

-- BEGIN COMPLETE MODULE ExitProbability
section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.Gundy.Proof
variable {Ω : Type*}

lemma exitStop_ne_top_iff_bad (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) :
    exitStop f l ω ≠ ⊤ ↔ ∃ N : ℕ, ω ∉ goodEvent f l N := by
  constructor
  · intro ht
    lift exitStop f l ω to ℕ using ht with k hk
    refine ⟨k,?_⟩
    intro hg
    have hh := (exitStop_gt_iff f l k ω).mpr hg
    rw [←hk] at hh
    exact (lt_irrefl _ hh)
  · rintro ⟨N,hN⟩ ht
    apply hN
    apply (exitStop_gt_iff f l N ω).mp
    rw [ht]
    exact WithTop.coe_lt_top N

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

lemma exit_probability_bound (hf : Martingale f ℱ P) {l : ℝ} (hl : 0 < l) :
    P {ω | exitStop f l ω ≠ ⊤} ≤ pNorm P 1 f / ENNReal.ofReal l := by
  have he : {ω | exitStop f l ω ≠ ⊤} = ⋃ N : ℕ, (goodEvent f l N)ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_compl_iff,exitStop_ne_top_iff_bad]
  have hmono : Monotone (fun N : ℕ => (goodEvent f l N)ᶜ) := by
    intro i j hij
    exact Set.compl_subset_compl.mpr (goodEvent_antitone f l hij)
  rw [he,hmono.measure_iUnion]
  apply iSup_le
  intro N
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hl)) (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm]
  exact finite_exit_probability_mul hf hl.le N

end BurkholderDFI.Gundy.Proof
end
-- END COMPLETE MODULE ExitProbability

-- BEGIN COMPLETE MODULE GundyRoot
section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.Gundy


theorem theorem_4_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤)
    (l : ℝ) (hl : 0 < l) :
    ∃ X Y Z : ℕ → Ω → ℝ, Martingale X ℱ P ∧ Martingale Y ℱ P ∧ Martingale Z ℱ P ∧
      (∀ n, 1 ≤ n → f n = X n + Y n + Z n) ∧
      BurkholderDFI.SquareFnLp.pNorm P 2 X ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * l) * BurkholderDFI.SquareFnLp.pNorm P 1 f ∧
      ∫⁻ ω, ∑' k : ℕ, ENNReal.ofReal |BurkholderDFI.SquareFnLp.dseq Y (k + 1) ω| ∂P ≤ 4 * BurkholderDFI.SquareFnLp.pNorm P 1 f ∧
      P {ω | 0 < BurkholderDFI.SquareFnLp.maxFn Z ω} ≤ BurkholderDFI.SquareFnLp.pNorm P 1 f / ENNReal.ofReal l := by
  let X := Proof.centeredProcess ℱ P (Proof.beforeInc f l)
  let S := stoppedProcess f (Proof.exitStop f l)
  have hX : Martingale X ℱ P := Proof.martingale_good_process hf hl.le
  have hS : Martingale S ℱ P := Proof.martingale_stopped hf
    (Proof.exitStop_isStoppingTime hf.stronglyAdapted l)
  refine ⟨X,S-X,f-S,hX,hS.sub hX,hf.sub hS,?_,?_,?_,?_⟩
  · intro n _
    funext ω
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  · exact Proof.good_process_pNorm hf hL1 hl.le
  · exact Proof.bad_process_variation hf hl.le
  · exact (measure_mono (Proof.remainder_support f l)).trans
      (Proof.exit_probability_bound hf hl)


end BurkholderDFI.Gundy

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤)
    (l : ℝ) (hl : 0 < l) :
    ∃ X Y Z : ℕ → Ω → ℝ, Martingale X ℱ P ∧ Martingale Y ℱ P ∧ Martingale Z ℱ P ∧
      (∀ n, 1 ≤ n → f n = X n + Y n + Z n) ∧
      BurkholderDFI.SquareFnLp.pNorm P 2 X ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * l) * BurkholderDFI.SquareFnLp.pNorm P 1 f ∧
      ∫⁻ ω, ∑' k : ℕ, ENNReal.ofReal |BurkholderDFI.SquareFnLp.dseq Y (k + 1) ω| ∂P ≤ 4 * BurkholderDFI.SquareFnLp.pNorm P 1 f ∧
      P {ω | 0 < BurkholderDFI.SquareFnLp.maxFn Z ω} ≤ BurkholderDFI.SquareFnLp.pNorm P 1 f / ENNReal.ofReal l := by
  exact BurkholderDFI.Gundy.theorem_4_1 hf hL1 l hl
end
-- END COMPLETE MODULE GundyRoot
