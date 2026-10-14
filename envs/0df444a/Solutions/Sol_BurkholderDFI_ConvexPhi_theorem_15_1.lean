-- Prove2me | solution 1 for BurkholderDFI.ConvexPhi.theorem_15_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T06:22:24.423475+00:00
-- url     : https://prove2.me/submissions/1fc49a5b-60e8-460f-b4a1-65950fa106f0

-- Complete checked reconstruction of the native convex moderate-growth BDG theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Mathlib


-- Begin Canonical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.ConvexPhi.Proof
open BurkholderDFI.SquareFnLp
end BurkholderDFI.ConvexPhi.Proof
-- End Canonical

-- Begin RecordBounds

namespace BurkholderDFI.ConvexPhi.Proof

noncomputable def runningAbs (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (runningAbs d n) |d (n + 1)|

lemma runningAbs_nonneg (d : ℕ → ℝ) (n : ℕ) : 0 ≤ runningAbs d n := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma runningAbs_mono (d : ℕ → ℝ) : Monotone (runningAbs d) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

lemma abs_le_runningAbs (d : ℕ → ℝ) {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    |d k| ≤ runningAbs d n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact (le_max_right _ _).trans (runningAbs_mono d hkn)

lemma runningAbs_le {d : ℕ → ℝ} {n : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ k, 0 < k → k ≤ n → |d k| ≤ b) : runningAbs d n ≤ b := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    exact max_le (ih (fun k hk hkn => h k hk (hkn.trans n.le_succ)))
      (h (n+1) (by omega) le_rfl)

noncomputable def largeIncrement (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if 2 * runningAbs d (k-1) < |d k| then d k else 0

lemma largeIncrement_abs_le (d : ℕ → ℝ) (k : ℕ) :
    |largeIncrement d k| ≤ |d k| := by
  unfold largeIncrement
  split_ifs <;> simp

lemma sum_largeIncrement_le (d : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, |largeIncrement d (k+1)| ≤ 2 * runningAbs d n := by
  induction n with
  | zero => simp [runningAbs]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [largeIncrement, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      if_false, Nat.add_sub_cancel]
    simp only [largeIncrement, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      if_false, Nat.add_sub_cancel] at ih
    by_cases h : 2 * runningAbs d n < |d (n+1)|
    · rw [if_pos h]
      have hmax : runningAbs d (n+1) = |d (n+1)| := by
        simp only [runningAbs]
        exact max_eq_right (by have := runningAbs_nonneg d n; linarith)
      rw [hmax]
      linarith
    · rw [if_neg h, abs_zero, add_zero]
      exact ih.trans (mul_le_mul_of_nonneg_left (runningAbs_mono d n.le_succ) (by norm_num))

lemma smallIncrement_bound (d : ℕ → ℝ) (k : ℕ) (hk : 0 < k) :
    |d k - largeIncrement d k| ≤ 2 * runningAbs d (k-1) := by
  unfold largeIncrement
  rw [if_neg hk.ne']
  split_ifs with h
  · simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (runningAbs_nonneg d (k-1))
  · simpa using le_of_not_gt h

end BurkholderDFI.ConvexPhi.Proof
-- End RecordBounds

-- Begin CenteredBasic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BurkholderDFI.ConvexPhi.Proof

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

end BurkholderDFI.ConvexPhi.Proof
-- End CenteredBasic

-- Begin CenteredL2

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

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

end BurkholderDFI.ConvexPhi.Proof
-- End CenteredL2

-- Begin IncrementProcess

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

noncomputable def partialProcess (e : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range n, e (k+1)

omit mΩ in
lemma partialProcess_zero (e : ℕ → Ω → ℝ) : partialProcess e 0 = 0 := by
  simp [partialProcess]

omit mΩ in
lemma partialProcess_succ (e : ℕ → Ω → ℝ) (n : ℕ) :
    partialProcess e (n+1) = partialProcess e n + e (n+1) := by
  simp [partialProcess, Finset.sum_range_succ]

lemma partialProcess_adapted {e : ℕ → Ω → ℝ} (he : StronglyAdapted ℱ e) :
    StronglyAdapted ℱ (partialProcess e) := by
  intro n
  exact Finset.stronglyMeasurable_sum _ fun k hk =>
    (he (k+1)).mono (ℱ.mono (by have := Finset.mem_range.mp hk; omega))

omit [IsFiniteMeasure P] in
lemma partialProcess_integrable {e : ℕ → Ω → ℝ} (he : ∀ k, Integrable (e k) P)
    (n : ℕ) : Integrable (partialProcess e n) P := by
  exact integrable_finsetSum' _ (fun k _ => he (k+1))

omit [IsFiniteMeasure P] in
lemma partialProcess_memLp {e : ℕ → Ω → ℝ} (he : ∀ k, MemLp (e k) 2 P)
    (n : ℕ) : MemLp (partialProcess e n) 2 P := by
  exact memLp_finsetSum' _ (fun k _ => he (k+1))

lemma martingale_partialProcess {e : ℕ → Ω → ℝ}
    (ha : StronglyAdapted ℱ e) (hi : ∀ k, Integrable (e k) P)
    (hz : ∀ k, P[e (k+1) | ℱ k] =ᵐ[P] 0) :
    Martingale (partialProcess e) ℱ P := by
  apply martingale_nat (partialProcess_adapted ha) (partialProcess_integrable hi)
  intro n
  rw [partialProcess_succ]
  refine ((condExp_add (partialProcess_integrable hi n) (hi (n+1)) _).trans ?_).symm
  rw [condExp_of_stronglyMeasurable (ℱ.le n) (partialProcess_adapted ha n)
    (partialProcess_integrable hi n)]
  filter_upwards [hz n] with ω hω
  simp only [Pi.add_apply, hω, Pi.zero_apply, add_zero]

lemma partialProcess_energy {e : ℕ → Ω → ℝ}
    (ha : StronglyAdapted ℱ e) (h2 : ∀ k, MemLp (e k) 2 P)
    (hz : ∀ k, P[e (k+1) | ℱ k] =ᵐ[P] 0) (n : ℕ) :
    (∫ ω, (partialProcess e n ω)^2 ∂P) =
      ∑ k ∈ Finset.range n, ∫ ω, (e (k+1) ω)^2 ∂P := by
  induction n with
  | zero => simp [partialProcess]
  | succ n ih =>
    have hc := integral_mul_condExp_eq (ℱ.le n)
      (partialProcess_adapted ha n) (partialProcess_memLp h2 n) (h2 (n+1))
    have hz' : (∫ ω, partialProcess e n ω * e (n+1) ω ∂P) = 0 := by
      rw [hc]
      calc
        _ = ∫ ω, (0:ℝ) ∂P := integral_congr_ae (by
          filter_upwards [hz n] with ω hω
          simp only [hω, Pi.zero_apply, mul_zero])
        _ = 0 := by simp
    rw [partialProcess_succ]
    change (∫ ω, (partialProcess e n ω + e (n+1) ω)^2 ∂P) = _
    rw [integral_square_add (partialProcess_memLp h2 n) (h2 (n+1)), hz', ih,
      Finset.sum_range_succ]
    ring

end BurkholderDFI.ConvexPhi.Proof
-- End IncrementProcess

-- Begin NativeIncrement

open MeasureTheory ProbabilityTheory
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

omit mΩ in
lemma native_dseq_zero (f : ℕ → Ω → ℝ) : dseq f 0 = 0 := by
  funext ω
  simp [dseq]

omit mΩ in
lemma native_dseq_one (f : ℕ → Ω → ℝ) : dseq f 1 = f 1 := by
  funext ω
  simp [dseq]

omit mΩ in
lemma native_dseq_succ (f : ℕ → Ω → ℝ) {k : ℕ} (hk : 0 < k) :
    dseq f (k+1) = f (k+1) - f k := by
  funext ω
  simp [dseq, hk.ne']

omit [IsFiniteMeasure P] in
lemma dseq_integrable {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (k : ℕ) :
    Integrable (dseq f k) P := by
  rcases k with _ | k
  · rw [native_dseq_zero]; exact integrable_zero Ω ℝ P
  rcases k with _ | k
  · rw [native_dseq_one]; exact hf.integrable 1
  · rw [native_dseq_succ f (by omega)]
    exact (hf.integrable _).sub (hf.integrable _)

lemma dseq_adapted {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (dseq f) := by
  intro k
  rcases k with _ | k
  · rw [native_dseq_zero]; exact stronglyMeasurable_const
  rcases k with _ | k
  · rw [native_dseq_one]; exact hf 1
  · rw [native_dseq_succ f (by omega)]
    exact (hf _).sub ((hf _).mono (ℱ.mono (Nat.le_succ _)))

lemma dseq_condExp_zero {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    {k : ℕ} (hk : 0 < k) : P[dseq f (k+1) | ℱ k] =ᵐ[P] 0 := by
  rw [native_dseq_succ f hk]
  refine (condExp_sub (hf.integrable (k+1)) (hf.integrable k) (ℱ k)).trans ?_
  rw [condExp_of_stronglyMeasurable (ℱ.le k) (hf.stronglyAdapted k) (hf.integrable k)]
  filter_upwards [hf.2 k (k+1) k.le_succ] with ω hω
  simp only [Pi.sub_apply, hω, sub_self, Pi.zero_apply]

omit mΩ in
lemma sum_dseq {f : ℕ → Ω → ℝ} {n : ℕ} (hn : 0 < n) (ω : Ω) :
    ∑ k ∈ Finset.range n, dseq f (k+1) ω = f n ω := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction n with
  | zero => simp [dseq]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [dseq, Nat.add_assoc]

lemma runningAbs_adapted {e : ℕ → Ω → ℝ} (he : StronglyAdapted ℱ e) :
    StronglyAdapted ℱ (fun n ω => runningAbs (fun k => e k ω) n) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    have h1 : StronglyMeasurable[ℱ (n+1)] (fun ω => runningAbs (fun k => e k ω) n) :=
      ih.mono (ℱ.mono n.le_succ)
    let : MeasurableSpace Ω := ℱ (n+1)
    exact (h1.measurable.max (he (n+1)).measurable.abs).stronglyMeasurable

omit [IsFiniteMeasure P] in
lemma runningAbs_integrable {e : ℕ → Ω → ℝ} (he : ∀ k, Integrable (e k) P) (n : ℕ) :
    Integrable (fun ω => runningAbs (fun k => e k ω) n) P := by
  induction n with
  | zero => exact (integrable_zero Ω ℝ P : Integrable (fun _ : Ω => (0:ℝ)) P)
  | succ n ih => exact ih.sup (he (n+1)).norm

end BurkholderDFI.ConvexPhi.Proof
-- End NativeIncrement

-- Begin DavisBasic

open MeasureTheory ProbabilityTheory
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

noncomputable def davisLarge (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  largeIncrement (fun j => dseq f j ω) k

noncomputable def davisSmall (f : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  dseq f k - davisLarge f k

lemma davisLarge_adapted {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (davisLarge f) := by
  intro k
  by_cases hk : k = 0
  · subst k
    exact stronglyMeasurable_const
  have he := dseq_adapted hf
  have hr := (runningAbs_adapted he (k-1)).mono (ℱ.mono (Nat.sub_le k 1))
  let : MeasurableSpace Ω := ℱ k
  have hs : MeasurableSet[ℱ k] {ω | 2 * runningAbs (fun j => dseq f j ω) (k-1) <
      |dseq f k ω|} := measurableSet_lt (measurable_const.mul hr.measurable) (he k).measurable.abs
  have hid : davisLarge f k = {ω | 2 * runningAbs (fun j => dseq f j ω) (k-1) <
      |dseq f k ω|}.indicator (dseq f k) := by
    funext ω
    simp only [davisLarge, largeIncrement, if_neg hk, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hid]
  exact (he k).indicator hs

omit [IsFiniteMeasure P] in
lemma davisLarge_integrable {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (k : ℕ) :
    Integrable (davisLarge f k) P := by
  apply (dseq_integrable hf k).abs.mono' ((davisLarge_adapted hf.stronglyAdapted k).mono (ℱ.le k)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs, davisLarge] using largeIncrement_abs_le (fun j => dseq f j ω) k

lemma davisSmall_adapted {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (davisSmall f) := by
  intro k
  exact (dseq_adapted hf k).sub (davisLarge_adapted hf k)

omit [IsFiniteMeasure P] in
lemma davisSmall_integrable {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (k : ℕ) :
    Integrable (davisSmall f k) P := (dseq_integrable hf k).sub (davisLarge_integrable hf k)

omit mΩ in
lemma davisSmall_one (f : ℕ → Ω → ℝ) : davisSmall f 1 = 0 := by
  funext ω
  simp only [davisSmall, Pi.sub_apply, davisLarge, largeIncrement, one_ne_zero,
    if_false, Nat.sub_self, runningAbs, mul_zero]
  by_cases h : 0 < |dseq f 1 ω|
  · rw [if_pos h, sub_self]; rfl
  · rw [if_neg h, sub_zero]
    exact abs_nonpos_iff.mp (le_of_not_gt h)

omit mΩ in
lemma davisSmall_bound (f : ℕ → Ω → ℝ) {k : ℕ} (hk : 0 < k) (ω : Ω) :
    |davisSmall f k ω| ≤ 2 * runningAbs (fun j => dseq f j ω) (k-1) :=
  smallIncrement_bound (fun j => dseq f j ω) k hk

omit mΩ in
lemma davisLarge_sum_bound (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range n, |davisLarge f (k+1) ω| ≤
      2 * runningAbs (fun j => dseq f j ω) n := sum_largeIncrement_le _ n

end BurkholderDFI.ConvexPhi.Proof
-- End DavisBasic

-- Begin ConditionalBound

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {m : MeasurableSpace Ω}

lemma abs_condExp_le_predictable (hm : m ≤ mΩ) {a b : Ω → ℝ}
    (ha : Integrable a P) (hb : Integrable b P) (hbm : StronglyMeasurable[m] b)
    (hab : ∀ᵐ ω ∂P, |a ω| ≤ b ω) : ∀ᵐ ω ∂P, |P[a|m] ω| ≤ b ω := by
  have h := condExp_mono (m := m) ha.abs hb hab
  rw [condExp_of_stronglyMeasurable hm hbm hb] at h
  exact (abs_condExp_ae_le_condExp_abs a).trans h

lemma centered_abs_le_predictable (hm : m ≤ mΩ) {a b : Ω → ℝ}
    (ha : Integrable a P) (hb : Integrable b P) (hbm : StronglyMeasurable[m] b)
    (hab : ∀ᵐ ω ∂P, |a ω| ≤ b ω) :
    ∀ᵐ ω ∂P, |a ω - P[a|m] ω| ≤ 2 * b ω := by
  filter_upwards [hab, abs_condExp_le_predictable (mΩ := mΩ) hm ha hb hbm hab] with ω h1 h2
  exact (abs_sub _ _).trans (by linarith)

end BurkholderDFI.ConvexPhi.Proof
-- End ConditionalBound

-- Begin DavisProcess

open MeasureTheory ProbabilityTheory
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

noncomputable def davisGood (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  centeredProcess ℱ P (davisSmall f)

lemma davisGood_martingale {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) :
    Martingale (davisGood ℱ P f) ℱ P :=
  martingale_centeredProcess (davisSmall_adapted hf.stronglyAdapted) (davisSmall_integrable hf)

omit [IsFiniteMeasure P] in
lemma davisGood_zero (f : ℕ → Ω → ℝ) : davisGood ℱ P f 0 = 0 := by
  rw [davisGood, centeredProcess_zero, davisSmall_one, condExp_zero]

omit [IsFiniteMeasure P] in
lemma davisGood_one (f : ℕ → Ω → ℝ) : davisGood ℱ P f 1 = 0 := by
  rw [davisGood, centeredProcess_one, davisSmall_one]

omit [IsFiniteMeasure P] in
lemma centeredProcess_dseq (a : ℕ → Ω → ℝ) (k : ℕ) :
    dseq (centeredProcess ℱ P a) (k+1) = centeredIncrement ℱ P a k := by
  funext ω
  cases k with
  | zero => simp [dseq, centeredProcess_one, centeredIncrement_zero]
  | succ k =>
    simp only [dseq, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [if_neg (by omega), centeredProcess_succ a (by omega)]
    simp

lemma davisGood_increment_bound {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (k : ℕ) :
    ∀ᵐ ω ∂P, |dseq (davisGood ℱ P f) (k+1) ω| ≤
      4 * runningAbs (fun j => dseq f j ω) k := by
  change ∀ᵐ ω ∂P, |dseq (centeredProcess ℱ P (davisSmall f)) (k+1) ω| ≤ _
  rw [centeredProcess_dseq]
  by_cases hk : k = 0
  · subst k
    rw [centeredIncrement_zero, davisSmall_one]
    exact Filter.Eventually.of_forall fun ω => by simp [runningAbs]
  · rw [centeredIncrement, if_neg hk]
    have hr := runningAbs_integrable (dseq_integrable hf) k
    have hm := runningAbs_adapted (dseq_adapted hf.stronglyAdapted) k
    have hb : ∀ᵐ ω ∂P, |davisSmall f (k+1) ω| ≤
        2 * runningAbs (fun j => dseq f j ω) k :=
      Filter.Eventually.of_forall fun ω => by
        simpa only [Nat.add_sub_cancel] using davisSmall_bound f (by omega : 0 < k+1) ω
    have h := centered_abs_le_predictable (mΩ := mΩ) (ℱ.le k)
      (davisSmall_integrable hf (k+1)) (hr.const_mul 2) (hm.const_mul 2) hb
    filter_upwards [h] with ω hω
    change |davisSmall f (k+1) ω - P[davisSmall f (k+1)|ℱ k] ω| ≤ _
    linarith

end BurkholderDFI.ConvexPhi.Proof
-- End DavisProcess

-- Begin DavisVariation

open MeasureTheory ProbabilityTheory
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

noncomputable def davisBad (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  f - davisGood ℱ P f

lemma davisBad_martingale {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) :
    Martingale (davisBad ℱ P f) ℱ P := hf.sub (davisGood_martingale hf)

omit mΩ in
lemma native_dseq_sub (f g : ℕ → Ω → ℝ) (k : ℕ) :
    dseq (f-g) k = dseq f k - dseq g k := by
  ext ω
  simp only [dseq, Pi.sub_apply]
  split_ifs <;> ring

lemma davisBad_increment_bound {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (k : ℕ) :
    ∀ᵐ ω ∂P, |dseq (davisBad ℱ P f) (k+1) ω| ≤ |davisLarge f (k+1) ω| +
      P[(fun ω => |davisLarge f (k+1) ω|)|ℱ k] ω := by
  have hnn := condExp_nonneg (μ := P) (m := ℱ k)
    (Filter.Eventually.of_forall fun ω => abs_nonneg (davisLarge f (k+1) ω))
  by_cases hk : k = 0
  · subst k
    filter_upwards [hnn] with ω hω
    have hz := congrFun (davisSmall_one f) ω
    have hg := congrFun (davisGood_one (ℱ := ℱ) (P := P) f) ω
    change dseq f 1 ω - davisLarge f 1 ω = 0 at hz
    have he : davisLarge f 1 ω = f 1 ω := by rw [native_dseq_one] at hz; linarith
    simp only [zero_add, davisBad, Pi.sub_apply, native_dseq_one, hg,
      Pi.zero_apply, sub_zero, he]
    change 0 ≤ P[(fun ω => |davisLarge f 1 ω|)|ℱ 0] ω at hω
    linarith
  · have hc : P[davisSmall f (k+1)|ℱ k] =ᵐ[P] -P[davisLarge f (k+1)|ℱ k] := by
      refine (condExp_sub (dseq_integrable hf (k+1)) (davisLarge_integrable hf (k+1)) (ℱ k)).trans ?_
      filter_upwards [dseq_condExp_zero hf (Nat.pos_of_ne_zero hk)] with ω hω
      simp only [Pi.sub_apply, hω, Pi.zero_apply, zero_sub, Pi.neg_apply]
    have ha := abs_condExp_ae_le_condExp_abs (μ := P) (m := ℱ k) (davisLarge f (k+1))
    filter_upwards [hc, ha] with ω hcω haω
    have hid : dseq (davisBad ℱ P f) (k+1) ω =
        davisLarge f (k+1) ω - P[davisLarge f (k+1)|ℱ k] ω := by
      rw [davisBad, native_dseq_sub]
      change dseq f (k+1) ω - dseq (centeredProcess ℱ P (davisSmall f)) (k+1) ω = _
      rw [centeredProcess_dseq, centeredIncrement, if_neg hk]
      change dseq f (k+1) ω - (davisSmall f (k+1) ω - P[davisSmall f (k+1)|ℱ k] ω) = _
      rw [hcω]
      change dseq f (k+1) ω - ((dseq f (k+1) ω-davisLarge f (k+1) ω) - (-P[davisLarge f (k+1)|ℱ k] ω)) = _
      ring
    rw [hid]
    have haω' : |P[davisLarge f (k+1)|ℱ k] ω| ≤ P[(fun ω => |davisLarge f (k+1) ω|)|ℱ k] ω := haω
    have ht := abs_sub (davisLarge f (k+1) ω) (P[davisLarge f (k+1)|ℱ k] ω)
    linarith

lemma davisBad_variation_bound {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (n : ℕ) :
    ∀ᵐ ω ∂P, (∑ k ∈ Finset.range n, |dseq (davisBad ℱ P f) (k+1) ω|) ≤
      (∑ k ∈ Finset.range n, |davisLarge f (k+1) ω|) +
      ∑ k ∈ Finset.range n, P[(fun ω => |davisLarge f (k+1) ω|)|ℱ k] ω := by
  filter_upwards [ae_all_iff.mpr (davisBad_increment_bound hf)] with ω hω
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => hω k

end BurkholderDFI.ConvexPhi.Proof
-- End DavisVariation

-- Begin PhiBasic

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp

noncomputable def phiReal (Φ : ℝ≥0∞ → ℝ≥0∞) (x : ℝ) : ℝ :=
  (Φ (ENNReal.ofReal x)).toReal

variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma phi_growth_pow (hΦ : IsPhi Φ c) (n : ℕ) (x : ℝ≥0∞) :
    Φ (2 ^ n * x) ≤ (c : ℝ≥0∞) ^ n * Φ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      Φ (2 ^ (n + 1) * x) = Φ (2 * (2 ^ n * x)) := by congr 1; ring
      _ ≤ c * Φ (2 ^ n * x) := hΦ.growth _
      _ ≤ c * ((c : ℝ≥0∞) ^ n * Φ x) := mul_le_mul' le_rfl ih
      _ = (c : ℝ≥0∞) ^ (n + 1) * Φ x := by ring

lemma phi_ofReal_ne_top (hΦ : IsPhi Φ c) (x : ℝ) : Φ (ENNReal.ofReal x) ≠ ⊤ := by
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const x
  have hp : Tendsto (fun n : ℕ => Φ (ENNReal.ofReal ((1 / 2 : ℝ) ^ n * x)))
      atTop (𝓝 0) := by
    have ht₁ := (ENNReal.continuous_ofReal.tendsto 0).comp ht
    have ht₂ := (hΦ.cont.tendsto (ENNReal.ofReal 0)).comp ht₁
    simpa only [Function.comp_def, ENNReal.ofReal_zero, hΦ.zero] using ht₂
  obtain ⟨n, hn⟩ := (hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).exists
  have heq : (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((1 / 2 : ℝ) ^ n * x) = ENNReal.ofReal x := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n * x) = (2 * (1 / 2 : ℝ)) ^ n * x := by rw [mul_pow]; ring
      _ = x := by norm_num
  have hb := phi_growth_pow hΦ n (ENNReal.ofReal ((1 / 2 : ℝ) ^ n * x))
  rw [heq] at hb
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ne_top_of_lt hn)) hb

lemma phiReal_nonneg (x : ℝ) : 0 ≤ phiReal Φ x := ENNReal.toReal_nonneg
lemma phiReal_zero (hΦ : IsPhi Φ c) : phiReal Φ 0 = 0 := by simp [phiReal, hΦ.zero]
lemma ofReal_phiReal (hΦ : IsPhi Φ c) (x : ℝ) : ENNReal.ofReal (phiReal Φ x) = Φ (ENNReal.ofReal x) :=
  ENNReal.ofReal_toReal (phi_ofReal_ne_top hΦ x)
lemma phiReal_mono (hΦ : IsPhi Φ c) : Monotone (phiReal Φ) := by
  intro x y hxy
  exact ENNReal.toReal_mono (phi_ofReal_ne_top hΦ y) (hΦ.mono (ENNReal.ofReal_le_ofReal hxy))
lemma phiReal_convex (hΦ : IsConvexPhi Φ) : ConvexOn ℝ (Set.Ici 0) (phiReal Φ) := hΦ
lemma phiReal_continuous (hΦ : IsPhi Φ c) : Continuous (phiReal Φ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have h₁ := (hΦ.cont.tendsto (ENNReal.ofReal x)).comp (ENNReal.continuous_ofReal.tendsto x)
  have h₂ := (ENNReal.tendsto_toReal (phi_ofReal_ne_top hΦ x)).comp h₁
  exact h₂

end BurkholderDFI.ConvexPhi.Proof
-- End PhiBasic

-- Begin PhiGrowth

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma phiReal_growth (hΦ : IsPhi Φ c) (x : ℝ) :
    phiReal Φ (2 * x) ≤ (c : ℝ) * phiReal Φ x := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (phi_ofReal_ne_top hΦ x)) (hΦ.growth (ENNReal.ofReal x))
  simpa [phiReal, ENNReal.ofReal_mul, ENNReal.toReal_mul] using h

lemma phiReal_growth_pow (hΦ : IsPhi Φ c) (n : ℕ) (x : ℝ) :
    phiReal Φ (2 ^ n * x) ≤ (c : ℝ) ^ n * phiReal Φ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      phiReal Φ (2 ^ (n+1) * x) = phiReal Φ (2 * (2 ^ n * x)) := by congr 1; ring
      _ ≤ c * phiReal Φ (2 ^ n * x) := phiReal_growth hΦ _
      _ ≤ c * ((c : ℝ) ^ n * phiReal Φ x) := mul_le_mul_of_nonneg_left ih c.coe_nonneg
      _ = (c : ℝ) ^ (n+1) * phiReal Φ x := by ring

lemma phiReal_add_le (hΦ : IsPhi Φ c) (x y : ℝ) :
    phiReal Φ (x+y) ≤ (c : ℝ) * (phiReal Φ x + phiReal Φ y) := by
  calc
    phiReal Φ (x+y) ≤ phiReal Φ (2 * max x y) := phiReal_mono hΦ (by have h₁ := le_max_left x y; have h₂ := le_max_right x y; linarith)
    _ ≤ c * phiReal Φ (max x y) := phiReal_growth hΦ _
    _ ≤ c * (phiReal Φ x + phiReal Φ y) := by
      apply mul_le_mul_of_nonneg_left _ c.coe_nonneg
      rcases le_total x y with h | h
      · rw [max_eq_right h]; exact le_add_of_nonneg_left (phiReal_nonneg x)
      · rw [max_eq_left h]; exact le_add_of_nonneg_right (phiReal_nonneg y)

lemma phiReal_lower_double (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) {x : ℝ} (hx : 0 ≤ x) :
    2 * phiReal Φ x ≤ phiReal Φ (2*x) := by
  have h := hcv.2 (show (0:ℝ) ∈ Set.Ici 0 from by simp)
    (show 2*x ∈ Set.Ici 0 from by change 0 ≤ 2*x; positivity)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2:ℝ)+1/2=1)
  change phiReal Φ ((1/2:ℝ) * 0 + (1/2:ℝ) * (2*x)) ≤
    (1/2:ℝ) * phiReal Φ 0 + (1/2:ℝ) * phiReal Φ (2*x) at h
  rw [phiReal_zero hΦ] at h
  have he : (1/2:ℝ) * 0 + (1/2:ℝ) * (2*x) = x := by ring
  rw [he] at h
  linarith

end BurkholderDFI.ConvexPhi.Proof
-- End PhiGrowth

-- Begin PhiDerivative

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

noncomputable def phiSlope (Φ : ℝ≥0∞ → ℝ≥0∞) (x : ℝ) : ℝ :=
  if 0 < x then derivWithin (phiReal Φ) (Ioi x) x else 0

lemma phiSlope_nonneg (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) (x : ℝ) :
    0 ≤ phiSlope Φ x := by
  unfold phiSlope
  split_ifs with hx
  · have hi : x ∈ interior (Ici (0:ℝ)) := by simpa using hx
    have hs := (phiReal_convex hcv).slope_le_leftDeriv_of_mem_interior (by simp) hi hx
    have hd := (phiReal_convex hcv).leftDeriv_le_rightDeriv_of_mem_interior hi
    have hn : 0 ≤ slope (phiReal Φ) 0 x := by
      rw [slope_def_field, phiReal_zero hΦ]
      exact div_nonneg (by simpa using phiReal_nonneg (Φ := Φ) x) (by simpa using hx.le)
    exact hn.trans (hs.trans hd)
  · exact le_rfl

lemma phiSlope_mono (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) : Monotone (phiSlope Φ) := by
  intro x y hxy
  by_cases hx : 0 < x
  · have hy := hx.trans_le hxy
    simp only [phiSlope, if_pos hx, if_pos hy]
    exact (phiReal_convex hcv).monotoneOn_rightDeriv (by simpa using hx) (by simpa using hy) hxy
  · rw [phiSlope, if_neg hx]
    exact phiSlope_nonneg hΦ hcv y

lemma phiSlope_measurable (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) : Measurable (phiSlope Φ) :=
  (phiSlope_mono hΦ hcv).measurable

lemma phiSlope_telescope (hcv : IsConvexPhi Φ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    phiReal Φ y - phiReal Φ x ≤ (y-x) * phiSlope Φ y := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  have hy : 0 < y := hx.trans_lt hlt
  have hi : y ∈ interior (Ici (0:ℝ)) := by simpa using hy
  have hs := (phiReal_convex hcv).slope_le_leftDeriv_of_mem_interior hx hi hlt
  have hd := (phiReal_convex hcv).leftDeriv_le_rightDeriv_of_mem_interior hi
  have h := hs.trans hd
  rw [slope_def_field] at h
  have he := (div_le_iff₀ (sub_pos.mpr hlt)).mp h
  simpa [phiSlope, hy, mul_comm] using he

lemma phiSlope_mul_le (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) {x : ℝ} (hx : 0 ≤ x) :
    x * phiSlope Φ x ≤ (c : ℝ) * phiReal Φ x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [zero_mul]
    exact mul_nonneg c.coe_nonneg (phiReal_nonneg 0)
  have hi : x ∈ interior (Ici (0:ℝ)) := by simpa using hx
  have hs := (phiReal_convex hcv).rightDeriv_le_slope_of_mem_interior hi
    (show 2*x ∈ Ici (0:ℝ) from by change 0 ≤ 2*x; positivity) (by linarith : x < 2*x)
  rw [slope_def_field] at hs
  have he := (le_div_iff₀ (by linarith : 0 < 2*x-x)).mp hs
  have hg := phiReal_growth hΦ x
  have hn := phiReal_nonneg (Φ := Φ) x
  simp only [phiSlope, if_pos hx]
  nlinarith

end BurkholderDFI.ConvexPhi.Proof
-- End PhiDerivative

-- Begin ConditionalWeight

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {Ω : Type*} {m0 m : MeasurableSpace Ω} {P : @Measure Ω m0}

lemma lintegral_condLExp_mul (hm : m ≤ m0) [SigmaFinite (P.trim hm)]
    {z q : Ω → ℝ≥0∞} (hz : Measurable[m0] z) (hq : Measurable[m] q) :
    (∫⁻ ω, (condLExp m P z ω) * q ω ∂P) = ∫⁻ ω, z ω * q ω ∂P := by
  have he : (P.withDensity (condLExp m P z)).trim hm = (P.withDensity z).trim hm := by
    apply Measure.ext
    intro S hS
    rw [trim_measurableSet_eq hm hS, trim_measurableSet_eq hm hS,
      withDensity_apply _ (hm S hS), withDensity_apply _ (hm S hS)]
    exact setLIntegral_condLExp hm P z hS
  have he := congrArg (fun μ : @Measure Ω m => ∫⁻ ω, q ω ∂μ) he
  rw [lintegral_trim hm hq, lintegral_trim hm hq,
    lintegral_withDensity_eq_lintegral_mul _ ((measurable_condLExp m P z).mono hm le_rfl) (hq.mono hm le_rfl),
    lintegral_withDensity_eq_lintegral_mul _ hz (hq.mono hm le_rfl)] at he
  exact he

lemma lintegral_condExp_mul (hm : m ≤ m0) [SigmaFinite (P.trim hm)]
    {z q : Ω → ℝ} (hz : Measurable[m0] z) (hzi : Integrable z P)
    (hz0 : 0 ≤ᵐ[P] z) (hq : Measurable[m] q) :
    (∫⁻ ω, ENNReal.ofReal ((P[z|m]) ω * q ω) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (z ω * q ω) ∂P := by
  have he := lintegral_condLExp_mul (P := P) hm hz.ennreal_ofReal hq.ennreal_ofReal
  have hc := condLExp_ofReal m hzi hz0
  calc
    (∫⁻ ω, ENNReal.ofReal ((P[z|m]) ω * q ω) ∂P) =
        ∫⁻ ω, (condLExp m P (fun ω => ENNReal.ofReal (z ω)) ω) * ENNReal.ofReal (q ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hc, condExp_nonneg hz0] with ω hω h0
      rw [hω, ENNReal.ofReal_mul h0]
    _ = ∫⁻ ω, ENNReal.ofReal (z ω) * ENNReal.ofReal (q ω) ∂P := he
    _ = ∫⁻ ω, ENNReal.ofReal (z ω * q ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hz0] with ω hω
      exact (ENNReal.ofReal_mul hω).symm

end BurkholderDFI.ConvexPhi.Proof
-- End ConditionalWeight

-- Begin CompensatorScalar

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma slope_young (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    {ε z w : ℝ} (hε : 0 < ε) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    z * phiSlope Φ w ≤ ε * c * phiReal Φ w + ε * c * phiReal Φ (z / ε) := by
  have hn := phiSlope_nonneg hΦ hcv w
  have hn₁ := phiReal_nonneg (Φ := Φ) w
  have hn₂ := phiReal_nonneg (Φ := Φ) (z/ε)
  by_cases h : z ≤ ε*w
  · have h₁ := mul_le_mul_of_nonneg_right h hn
    have h₂ := mul_le_mul_of_nonneg_left (phiSlope_mul_le hΦ hcv hw) hε.le
    nlinarith [mul_nonneg (mul_nonneg hε.le c.coe_nonneg) hn₂]
  · have h₁ : w ≤ z/ε := (le_div_iff₀ hε).mpr (by linarith)
    have h₂ := mul_le_mul_of_nonneg_left (phiSlope_mono hΦ hcv h₁) hz
    have h₃ := mul_le_mul_of_nonneg_left (phiSlope_mul_le hΦ hcv (div_nonneg hz hε.le)) hε.le
    have he : ε * (z/ε) = z := mul_div_cancel₀ z (ne_of_gt hε)
    rw [← mul_assoc ε, he] at h₃
    nlinarith [mul_nonneg (mul_nonneg hε.le c.coe_nonneg) hn₁]

lemma phi_prefix_telescope (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (n : ℕ) :
    phiReal Φ (∑ k ∈ Finset.range n, w k) ≤
      ∑ k ∈ Finset.range n, w k * phiSlope Φ (∑ j ∈ Finset.range (k+1), w j) := by
  induction n with
  | zero => simp [phiReal_zero hΦ]
  | succ n ih =>
    have hn : 0 ≤ ∑ k ∈ Finset.range n, w k := Finset.sum_nonneg fun k _ => hw k
    have ht := phiSlope_telescope hcv hn (le_add_of_nonneg_right (hw n))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    simp only [add_sub_cancel_left] at ht
    linarith

end BurkholderDFI.ConvexPhi.Proof
-- End CompensatorScalar

-- Begin CompensatorBasic

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
variable {ℱ : Filtration ℕ mΩ}

noncomputable def compensator (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (z : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range n, (P[z k | ℱ k]) ω

lemma compensator_measurable (z : ℕ → Ω → ℝ) (t : ℕ) :
    Measurable[ℱ t] (compensator ℱ P z (t+1)) := by
  apply Finset.measurable_sum
  intro k hk
  exact (stronglyMeasurable_condExp (μ := P) (m := ℱ k) (f := z k)).measurable.mono
    (ℱ.mono (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk))) le_rfl

lemma compensator_nonneg {z : ℕ → Ω → ℝ} (hz : ∀ k, 0 ≤ᵐ[P] z k) :
    ∀ᵐ ω ∂P, ∀ n, 0 ≤ compensator ℱ P z n ω := by
  have hw : ∀ᵐ ω ∂P, ∀ k, 0 ≤ (P[z k | ℱ k]) ω :=
    ae_all_iff.mpr fun k => condExp_nonneg (hz k)
  filter_upwards [hw] with ω hω n
  exact Finset.sum_nonneg fun k _ => hω k

lemma compensator_mono {z : ℕ → Ω → ℝ} (hz : ∀ k, 0 ≤ᵐ[P] z k) :
    ∀ᵐ ω ∂P, Monotone (fun n => compensator ℱ P z n ω) := by
  have hw : ∀ᵐ ω ∂P, ∀ k, 0 ≤ (P[z k | ℱ k]) ω :=
    ae_all_iff.mpr fun k => condExp_nonneg (hz k)
  filter_upwards [hw] with ω hω
  exact monotone_nat_of_le_succ fun n => by
    simp only [compensator, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hω n)

lemma compensator_integrable (z : ℕ → Ω → ℝ) (n : ℕ) :
    Integrable (compensator ℱ P z n) P := by
  exact integrable_finsetSum _ fun k _ => integrable_condExp

end BurkholderDFI.ConvexPhi.Proof
-- End CompensatorBasic

-- Begin PhiIntegrable

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

omit [IsProbabilityMeasure P] in
lemma integrable_phi_add (hΦ : IsPhi Φ c) {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hfi : Integrable (fun ω => phiReal Φ (f ω)) P)
    (hgi : Integrable (fun ω => phiReal Φ (g ω)) P) :
    Integrable (fun ω => phiReal Φ (f ω+g ω)) P := by
  apply ((hfi.add hgi).const_mul (c : ℝ)).mono'
    ((phiReal_continuous hΦ).comp_aestronglyMeasurable (hf.add hg))
  exact ae_of_all _ fun ω => by
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (phiReal_nonneg _)] using phiReal_add_le hΦ (f ω) (g ω)

lemma integrable_phi_sum {ι : Type*} (hΦ : IsPhi Φ c) (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) P)
    (hi : ∀ i ∈ s, Integrable (fun ω => phiReal Φ (f i ω)) P) :
    Integrable (fun ω => phiReal Φ (∑ i ∈ s, f i ω)) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phiReal_zero hΦ]
  | @insert i s his ih =>
    simp only [Finset.mem_insert] at hf hi
    have hs := ih (fun j hj => hf j (Or.inr hj)) (fun j hj => hi j (Or.inr hj))
    have ha := integrable_phi_add hΦ (hf i (Or.inl rfl))
      (show AEStronglyMeasurable (fun ω => ∑ j ∈ s, f j ω) P from by convert (Finset.aestronglyMeasurable_sum s fun j hj => hf j (Or.inr hj)) using 1; ext ω; simp) (hi i (Or.inl rfl)) hs
    simpa only [Finset.sum_insert his] using ha

lemma integrable_phi_condExp (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ}
    (hf : Integrable f P) (hf0 : 0 ≤ᵐ[P] f) (hphi : Integrable (fun ω => phiReal Φ (f ω)) P) :
    Integrable (fun ω => phiReal Φ ((P[f|m]) ω)) P := by
  have hj := (phiReal_convex hcv).map_condExp_le hm ((phiReal_continuous hΦ).lowerSemicontinuous.lowerSemicontinuousOn _)
    hf0 isClosed_Ici hf hphi
  apply (integrable_condExp (μ := P) (m := m) (f := fun ω => phiReal Φ (f ω))).mono'
    ((phiReal_continuous hΦ).comp_aestronglyMeasurable ((stronglyMeasurable_condExp (μ := P) (m := m) (f := f)).mono hm).aestronglyMeasurable)
  filter_upwards [hj] with ω hω
  simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (phiReal_nonneg _)] using hω

end BurkholderDFI.ConvexPhi.Proof
-- End PhiIntegrable

-- Begin CompensatorIntegrable

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} {ℱ : Filtration ℕ mΩ}

lemma compensator_phi_integrable (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k)) (hzi : ∀ k, Integrable (z k) P)
    (hz0 : ∀ k ω, 0 ≤ z k ω) (n : ℕ)
    (hi : Integrable (fun ω => phiReal Φ (∑ k ∈ Finset.range n, z k ω)) P) :
    Integrable (fun ω => phiReal Φ (compensator ℱ P z n ω)) P := by
  apply integrable_phi_sum hΦ (Finset.range n) (fun k => P[z k | ℱ k])
  · intro k _
    exact (stronglyMeasurable_condExp (μ := P) (m := ℱ k) (f := z k)).mono (ℱ.le k) |>.aestronglyMeasurable
  · intro k hk
    apply integrable_phi_condExp hΦ hcv (ℱ.le k) (hzi k) (ae_of_all _ (hz0 k))
    apply hi.mono' ((phiReal_continuous hΦ).comp_aestronglyMeasurable (hz k).aestronglyMeasurable)
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (phiReal_nonneg _)]
      exact phiReal_mono hΦ (Finset.single_le_sum (fun j _ => hz0 j ω) hk)

end BurkholderDFI.ConvexPhi.Proof
-- End CompensatorIntegrable

-- Begin CompensatorWeight

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} {ℱ : Filtration ℕ mΩ}

omit [IsProbabilityMeasure P] in
lemma lintegral_ofReal_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i)) (h0 : ∀ᵐ ω ∂P, ∀ i ∈ s, 0 ≤ f i ω) :
    (∫⁻ ω, ENNReal.ofReal (∑ i ∈ s, f i ω) ∂P) =
      ∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal (f i ω) ∂P := by
  calc
    _ = ∫⁻ ω, ∑ i ∈ s, ENNReal.ofReal (f i ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [h0] with ω hω
      exact ENNReal.ofReal_sum_of_nonneg hω
    _ = _ := lintegral_finsetSum s fun i hi => (hm i hi).ennreal_ofReal

lemma compensator_weight_bound (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    (z : ℕ → Ω → ℝ) (hz : ∀ k, Measurable (z k)) (hzi : ∀ k, Integrable (z k) P)
    (hz0 : ∀ k ω, 0 ≤ z k ω) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (phiReal Φ (compensator ℱ P z n ω)) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range n, z k ω) *
        phiSlope Φ (compensator ℱ P z n ω)) ∂P := by
  let w : ℕ → Ω → ℝ := fun k => P[z k | ℱ k]
  let q : ℕ → Ω → ℝ := fun k ω => phiSlope Φ (compensator ℱ P z (k+1) ω)
  have hw : ∀ᵐ ω ∂P, ∀ k, 0 ≤ w k ω := ae_all_iff.mpr fun k => condExp_nonneg (ae_of_all _ (hz0 k))
  have hq (k : ℕ) : Measurable[ℱ k] (q k) := (phiSlope_measurable hΦ hcv).comp (compensator_measurable z k)
  have hq0 (k : ℕ) (ω : Ω) : 0 ≤ q k ω := phiSlope_nonneg hΦ hcv _
  have hwm (k : ℕ) : Measurable (w k) := stronglyMeasurable_condExp.measurable.mono (ℱ.le k) le_rfl
  have hqm (k : ℕ) : Measurable (q k) := (hq k).mono (ℱ.le k) le_rfl
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.range n, w k ω * q k ω) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hw] with ω hω
      exact ENNReal.ofReal_le_ofReal (phi_prefix_telescope hΦ hcv (fun k => w k ω) hω n)
    _ = ∑ k ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal (w k ω * q k ω) ∂P := by
      apply lintegral_ofReal_finsetSum _ _ (fun k _ => (hwm k).mul (hqm k))
      filter_upwards [hw] with ω hω k _
      exact mul_nonneg (hω k) (hq0 k ω)
    _ = ∑ k ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal (z k ω * q k ω) ∂P := by
      apply Finset.sum_congr rfl
      intro k _
      exact lintegral_condExp_mul (ℱ.le k) (hz k) (hzi k) (ae_of_all _ (hz0 k)) (hq k)
    _ = ∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.range n, z k ω * q k ω) ∂P := by
      symm
      apply lintegral_ofReal_finsetSum _ _ (fun k _ => (hz k).mul (hqm k))
      exact ae_of_all _ fun ω k _ => mul_nonneg (hz0 k ω) (hq0 k ω)
    _ ≤ _ := by
      apply lintegral_mono_ae
      have hmono := compensator_mono (ℱ := ℱ) (fun k => ae_of_all P (hz0 k))
      filter_upwards [hmono] with ω hω
      apply ENNReal.ofReal_le_ofReal
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (phiSlope_mono hΦ hcv (hω (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))) (hz0 k ω)

end BurkholderDFI.ConvexPhi.Proof
-- End CompensatorWeight

-- Begin CompensatorYoung

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma slope_young_dyadic (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    (k : ℕ) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) :
    z * phiSlope Φ w ≤ ((1/2:ℝ)^k * c) * phiReal Φ w +
      ((1/2:ℝ)^k * (c : ℝ)^(k+1)) * phiReal Φ z := by
  have hp : 0 < (1/2:ℝ)^k := by positivity
  have h := slope_young hΦ hcv hp hz hw
  have he : z / (1/2:ℝ)^k = 2^k * z := by simp [div_eq_mul_inv, mul_comm]
  rw [he] at h
  have hg := mul_le_mul_of_nonneg_left (phiReal_growth_pow hΦ k z)
    (mul_nonneg hp.le c.coe_nonneg)
  calc
    _ ≤ _ := h
    _ ≤ ((1/2:ℝ)^k * c) * phiReal Φ w +
        ((1/2:ℝ)^k * c) * ((c : ℝ)^k * phiReal Φ z) := add_le_add le_rfl hg
    _ = _ := by ring

lemma lintegral_linear_nonneg {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : 0 ≤ᵐ[P] f) (hg0 : 0 ≤ᵐ[P] g) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ ω, ENNReal.ofReal (a*f ω+b*g ω) ∂P) =
      ENNReal.ofReal a * (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) +
      ENNReal.ofReal b * (∫⁻ ω, ENNReal.ofReal (g ω) ∂P) := by
  calc
    _ = ∫⁻ ω, ENNReal.ofReal a * ENNReal.ofReal (f ω) + ENNReal.ofReal b * ENNReal.ofReal (g ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hf0, hg0] with ω hω hω'
      rw [ENNReal.ofReal_add (mul_nonneg ha hω) (mul_nonneg hb hω'), ENNReal.ofReal_mul ha,
        ENNReal.ofReal_mul hb]
    _ = _ := by
      rw [lintegral_add_left (show Measurable (fun ω => ENNReal.ofReal a * ENNReal.ofReal (f ω)) from measurable_const.mul hf.ennreal_ofReal),
        lintegral_const_mul _ hf.ennreal_ofReal, lintegral_const_mul _ hg.ennreal_ofReal]

lemma ennreal_absorb_half {A B r s : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hr : r ≤ 1/2) (hs : s ≠ ⊤) (h : A ≤ r*A+s*B) : A ≤ 2*s*B := by
  have hr' : r ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hr
  have hR : r*A+s*B ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top hr' hA, ENNReal.mul_ne_top hs hB⟩
  have hh := (ENNReal.toReal_le_toReal hA hR).mpr h
  have hrr := ENNReal.toReal_mono (by norm_num : (1/2:ℝ≥0∞) ≠ ⊤) hr
  simp only [ENNReal.toReal_add (ENNReal.mul_ne_top hr' hA) (ENNReal.mul_ne_top hs hB),
    ENNReal.toReal_mul] at hh
  norm_num at hrr
  apply (ENNReal.toReal_le_toReal hA (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hs) hB)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  nlinarith [ENNReal.toReal_nonneg (a := A)]

end BurkholderDFI.ConvexPhi.Proof
-- End CompensatorYoung

-- Begin CompensatorBound

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} {ℱ : Filtration ℕ mΩ}

lemma compensator_bound_dyadic (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    (k : ℕ) (hk : (1/2:ℝ)^k * c ≤ 1/2)
    (z : ℕ → Ω → ℝ) (hz : ∀ j, Measurable (z j)) (hzi : ∀ j, Integrable (z j) P)
    (hz0 : ∀ j ω, 0 ≤ z j ω) (n : ℕ) :
    (∫⁻ ω, Φ (ENNReal.ofReal (compensator ℱ P z n ω)) ∂P) ≤
      (1 + 2 * ENNReal.ofReal ((1/2:ℝ)^k * (c:ℝ)^(k+1))) *
        ∫⁻ ω, Φ (ENNReal.ofReal (∑ j ∈ Finset.range n, z j ω)) ∂P := by
  let Z : Ω → ℝ := fun ω => ∑ j ∈ Finset.range n, z j ω
  let W : Ω → ℝ := compensator ℱ P z n
  let A := ∫⁻ ω, ENNReal.ofReal (phiReal Φ (W ω)) ∂P
  let B := ∫⁻ ω, ENNReal.ofReal (phiReal Φ (Z ω)) ∂P
  have hZm : Measurable Z := Finset.measurable_sum _ fun j _ => hz j
  have hWm : Measurable W := Finset.measurable_sum _ fun j _ =>
    stronglyMeasurable_condExp.measurable.mono (ℱ.le j) le_rfl
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => Finset.sum_nonneg fun j _ => hz0 j ω
  have hW0 : 0 ≤ᵐ[P] W := (compensator_nonneg (ℱ := ℱ) (fun j => ae_of_all P (hz0 j))).mono fun _ h => h n
  simp_rw [← ofReal_phiReal hΦ]
  change A ≤ (1+2*ENNReal.ofReal ((1/2:ℝ)^k*(c:ℝ)^(k+1)))*B
  by_cases hB : B = ⊤
  · rw [hB, ENNReal.mul_top (by positivity)]
    exact le_top
  have hBi : Integrable (fun ω => phiReal Φ (Z ω)) P :=
    ⟨(phiReal_continuous hΦ).comp_aestronglyMeasurable hZm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => phiReal_nonneg (Z ω))).mpr (lt_top_iff_ne_top.mpr hB)⟩
  have hAi := compensator_phi_integrable (ℱ := ℱ) hΦ hcv z hz hzi hz0 n hBi
  have hA : A ≠ ⊤ := ((hasFiniteIntegral_iff_ofReal
    (ae_of_all P fun ω => phiReal_nonneg (W ω))).mp hAi.hasFiniteIntegral).ne
  have hle : A ≤ ENNReal.ofReal ((1/2:ℝ)^k*c)*A +
      ENNReal.ofReal ((1/2:ℝ)^k*(c:ℝ)^(k+1))*B := by
    calc
      A ≤ ∫⁻ ω, ENNReal.ofReal (Z ω * phiSlope Φ (W ω)) ∂P :=
        compensator_weight_bound hΦ hcv z hz hzi hz0 n
      _ ≤ ∫⁻ ω, ENNReal.ofReal (((1/2:ℝ)^k*c)*phiReal Φ (W ω) +
          ((1/2:ℝ)^k*(c:ℝ)^(k+1))*phiReal Φ (Z ω)) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hW0] with ω hω
        exact ENNReal.ofReal_le_ofReal (slope_young_dyadic hΦ hcv k (hZ0 ω) hω)
      _ = _ := lintegral_linear_nonneg ((phiReal_continuous hΦ).measurable.comp hWm)
        ((phiReal_continuous hΦ).measurable.comp hZm)
        (ae_of_all _ fun ω => phiReal_nonneg (W ω)) (ae_of_all _ fun ω => phiReal_nonneg (Z ω))
        (by positivity) (by positivity)
  have hr : ENNReal.ofReal ((1/2:ℝ)^k*c) ≤ 1/2 := by
    exact (ENNReal.ofReal_le_ofReal hk).trans_eq (by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num)
  exact (ennreal_absorb_half hA hB hr ENNReal.ofReal_ne_top hle).trans
    (mul_le_mul' (le_add_of_nonneg_left (by positivity)) le_rfl)

end BurkholderDFI.ConvexPhi.Proof
-- End CompensatorBound

-- Begin CompensatorUniform

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp

lemma exists_compensator_scale (c : ℝ≥0) : ∃ k : ℕ, (1/2:ℝ)^k * c ≤ 1/2 := by
  have ht : Tendsto (fun k : ℕ => (1/2:ℝ)^k * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const (c:ℝ)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).exists
  exact ⟨k, hk.le⟩

lemma compensator_uniform (c : ℝ≥0) : ∃ K : ℝ≥0, 0 < K ∧
    ∀ (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (Φ : ℝ≥0∞ → ℝ≥0∞), IsPhi Φ c → IsConvexPhi Φ →
    ∀ (z : ℕ → Ω → ℝ), (∀ j, Measurable (z j)) → (∀ j, Integrable (z j) P) →
      (∀ j ω, 0 ≤ z j ω) → ∀ n,
      (∫⁻ ω, Φ (ENNReal.ofReal (compensator ℱ P z n ω)) ∂P) ≤
        K * ∫⁻ ω, Φ (ENNReal.ofReal (∑ j ∈ Finset.range n, z j ω)) ∂P := by
  obtain ⟨k, hk⟩ := exists_compensator_scale c
  refine ⟨1+2*((1/2:ℝ≥0)^k*c^(k+1)), by positivity, ?_⟩
  intro Ω mΩ P hP ℱ Φ hΦ hcv z hz hzi hz0 n
  have h := compensator_bound_dyadic (ℱ := ℱ) hΦ hcv k hk z hz hzi hz0 n
  convert h using 1
  push_cast
  simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, inv_pow, ENNReal.inv_pow]

end BurkholderDFI.ConvexPhi.Proof
-- End CompensatorUniform

-- Begin OrliczMoment

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

noncomputable def phiMoment (P : Measure Ω) (Φ : ℝ≥0∞ → ℝ≥0∞) (X : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, Φ (ENNReal.ofReal (X ω)) ∂P

lemma phi_add_le (hΦ : IsPhi Φ c) (x y : ℝ≥0∞) : Φ (x+y) ≤ c*(Φ x+Φ y) := by
  have hxy : x+y ≤ 2*max x y := by
    simpa only [two_mul] using add_le_add (le_max_left x y) (le_max_right x y)
  refine (hΦ.mono hxy).trans ((hΦ.growth _).trans (mul_le_mul' le_rfl ?_))
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact le_add_of_nonneg_left zero_le
  · rw [max_eq_left h]; exact le_add_of_nonneg_right zero_le

lemma phiMoment_mono (hΦ : IsPhi Φ c) {X Y : Ω → ℝ} (h : X ≤ᵐ[P] Y) :
    phiMoment P Φ X ≤ phiMoment P Φ Y := by
  apply lintegral_mono_ae
  filter_upwards [h] with ω hω
  exact hΦ.mono (ENNReal.ofReal_le_ofReal hω)

lemma phiMoment_congr {X Y : Ω → ℝ} (h : X =ᵐ[P] Y) : phiMoment P Φ X = phiMoment P Φ Y :=
  lintegral_congr_ae (h.fun_comp fun x => Φ (ENNReal.ofReal x))

lemma phiMoment_add_bound (hΦ : IsPhi Φ c) {X Y Z : Ω → ℝ}
    (hY : Measurable Y) (_hZ : Measurable Z) (h : X ≤ᵐ[P] (fun ω => Y ω+Z ω)) :
    phiMoment P Φ X ≤ c*(phiMoment P Φ Y+phiMoment P Φ Z) := by
  calc
    _ ≤ ∫⁻ ω, c*(Φ (ENNReal.ofReal (Y ω))+Φ (ENNReal.ofReal (Z ω))) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [h] with ω hω
      exact (hΦ.mono ((ENNReal.ofReal_le_ofReal hω).trans ENNReal.ofReal_add_le)).trans (phi_add_le hΦ _ _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        lintegral_add_left (show Measurable (fun ω => Φ (ENNReal.ofReal (Y ω))) from
          hΦ.cont.measurable.comp hY.ennreal_ofReal)]
      rfl

lemma phiMoment_scale_pow (hΦ : IsPhi Φ c) (X : Ω → ℝ) (k : ℕ) :
    phiMoment P Φ (fun ω => 2^k*X ω) ≤ (c:ℝ≥0∞)^k*phiMoment P Φ X := by
  calc
    _ ≤ ∫⁻ ω, (c:ℝ≥0∞)^k*Φ (ENNReal.ofReal (X ω)) ∂P := by
      apply lintegral_mono
      intro ω
      change Φ (ENNReal.ofReal (2^k*X ω)) ≤ (c:ℝ≥0∞)^k*Φ (ENNReal.ofReal (X ω))
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      exact phi_growth_pow hΦ k _
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

end BurkholderDFI.ConvexPhi.Proof
-- End OrliczMoment

-- Begin FiniteNorms

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*}

noncomputable def maxReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (maxFnN f n ω).toReal
noncomputable def squareReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2)

lemma maxFnN_ne_top (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : maxFnN f n ω ≠ ⊤ := by
  apply ne_top_of_le_ne_top ((show ENNReal.ofReal (∑ k ∈ Finset.Icc 1 n, |f k ω|) ≠ ⊤ from ENNReal.ofReal_ne_top))
  apply iSup_le fun k => iSup_le fun hk => ?_
  exact ENNReal.ofReal_le_ofReal (Finset.single_le_sum (fun j _ => abs_nonneg (f j ω)) hk)
lemma maxReal_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ maxReal f n ω :=
  ENNReal.toReal_nonneg
lemma squareReal_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ squareReal f n ω :=
  Real.sqrt_nonneg _
lemma ofReal_maxReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (maxReal f n ω) = maxFnN f n ω :=
  ENNReal.ofReal_toReal (maxFnN_ne_top f n ω)
lemma ofReal_squareReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (squareReal f n ω) = sqFnN f n ω := rfl
lemma abs_le_maxReal (f : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) (ω : Ω) :
    |f k ω| ≤ maxReal f n ω := by
  apply (ENNReal.ofReal_le_ofReal_iff (maxReal_nonneg f n ω)).mp
  rw [ofReal_maxReal]
  exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)
lemma maxReal_le (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ k ∈ Finset.Icc 1 n, |f k ω| ≤ b) : maxReal f n ω ≤ b := by
  apply (ENNReal.ofReal_le_ofReal_iff hb).mp
  rw [ofReal_maxReal]
  exact iSup_le fun k => iSup_le fun hk => ENNReal.ofReal_le_ofReal (h k hk)
lemma maxReal_zero (f : ℕ → Ω → ℝ) (ω : Ω) : maxReal f 0 ω = 0 := by
  simp [maxReal, maxFnN]
lemma squareReal_zero (f : ℕ → Ω → ℝ) (ω : Ω) : squareReal f 0 ω = 0 := by
  simp [squareReal]
lemma squareReal_sq (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    squareReal f n ω ^ 2 = ∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg (dseq f k ω))

end BurkholderDFI.ConvexPhi.Proof
-- End FiniteNorms

-- Begin FiniteNormTriangle

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*}

lemma dseq_add (f g : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    dseq (f+g) k ω = dseq f k ω + dseq g k ω := by
  simp only [dseq, Pi.add_apply]
  split_ifs <;> ring_nf

lemma maxReal_add_le (f g : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxReal (f+g) n ω ≤ maxReal f n ω + maxReal g n ω := by
  apply maxReal_le _ _ _ (add_nonneg (maxReal_nonneg _ _ _) (maxReal_nonneg _ _ _))
  intro k hk
  exact (abs_add_le (f k ω) (g k ω)).trans (add_le_add (abs_le_maxReal f hk ω) (abs_le_maxReal g hk ω))

lemma squareReal_add_le (f g : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    squareReal (f+g) n ω ≤ squareReal f n ω + squareReal g n ω := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Icc 1 n) (fun k => dseq f k ω) (fun k => dseq g k ω)
  change (∑ k ∈ Finset.Icc 1 n, dseq f k ω*dseq g k ω) ≤ squareReal f n ω*squareReal g n ω at hc
  have he : squareReal (f+g) n ω ^ 2 = squareReal f n ω ^ 2 + squareReal g n ω ^ 2 +
      2*(∑ k ∈ Finset.Icc 1 n, dseq f k ω*dseq g k ω) := by
    simp only [squareReal_sq, dseq_add, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  have hf := squareReal_nonneg f n ω
  have hg := squareReal_nonneg g n ω
  have hfg := squareReal_nonneg (f+g) n ω
  nlinarith

lemma squareReal_le_variation (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    squareReal f n ω ≤ ∑ k ∈ Finset.Icc 1 n, |dseq f k ω| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.Icc 1 n) (f := fun k => |dseq f k ω|)
    (fun k _ => abs_nonneg _)
  simp only [sq_abs] at hs
  rw [← squareReal_sq] at hs
  have hn := Finset.sum_nonneg (s := Finset.Icc 1 n) (fun k _ => abs_nonneg (dseq f k ω))
  nlinarith [squareReal_nonneg f n ω]

lemma dseq_le_squareReal (f : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) (ω : Ω) :
    |dseq f k ω| ≤ squareReal f n ω := by
  have hs := Finset.single_le_sum (s := Finset.Icc 1 n) (f := fun j => dseq f j ω ^ 2)
    (fun j _ => sq_nonneg _) hk
  rw [← squareReal_sq] at hs
  nlinarith [sq_abs (dseq f k ω), abs_nonneg (dseq f k ω), squareReal_nonneg f n ω]

lemma maxReal_dseq_le_squareReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxReal (dseq f) n ω ≤ squareReal f n ω :=
  maxReal_le _ _ _ (squareReal_nonneg _ _ _) (fun _ hk => dseq_le_squareReal f hk ω)

lemma maxReal_dseq_le_maxReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxReal (dseq f) n ω ≤ 2*maxReal f n ω := by
  apply maxReal_le _ _ _ (mul_nonneg (by norm_num) (maxReal_nonneg f n ω))
  intro k hk
  have hk₁ := (Finset.mem_Icc.mp hk).1
  have hk₂ := (Finset.mem_Icc.mp hk).2
  by_cases hk1 : k=1
  · simpa [dseq, hk1] using (abs_le_maxReal f hk ω).trans (by nlinarith [maxReal_nonneg f n ω])
  · have hk0 : k ≠ 0 := by omega
    simp only [dseq, if_neg hk0, if_neg hk1]
    have h₁ := abs_le_maxReal f hk ω
    have h₂ := abs_le_maxReal f (show k-1 ∈ Finset.Icc 1 n from Finset.mem_Icc.mpr ⟨by omega, by omega⟩) ω
    have h₃ : |f k ω-f (k-1) ω| ≤ |f k ω|+|f (k-1) ω| := by simpa using abs_sub_le (f k ω) 0 (f (k-1) ω)
    linarith

end BurkholderDFI.ConvexPhi.Proof
-- End FiniteNormTriangle

-- Begin FiniteVariation

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*}

lemma real_sum_Icc_one_eq_range (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, a k) = ∑ k ∈ Finset.range n, a (k+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

noncomputable def variationReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, |dseq f (k+1) ω|

lemma variationReal_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ variationReal f n ω :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma squareReal_le_variationReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    squareReal f n ω ≤ variationReal f n ω := by
  simpa only [real_sum_Icc_one_eq_range, variationReal] using squareReal_le_variation f n ω

lemma maxReal_le_variationReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxReal f n ω ≤ variationReal f n ω := by
  apply maxReal_le _ _ _ (variationReal_nonneg _ _ _)
  intro k hk
  have hk0 := (Finset.mem_Icc.mp hk).1
  have hkn := (Finset.mem_Icc.mp hk).2
  calc
    |f k ω| = |∑ j ∈ Finset.range k, dseq f (j+1) ω| := by rw [sum_dseq (by omega)]
    _ ≤ ∑ j ∈ Finset.range k, |dseq f (j+1) ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ variationReal f n ω := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkn)
      (fun _ _ _ => abs_nonneg _)

lemma dseq_neg (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : dseq (-f) k ω = -dseq f k ω := by
  simp only [dseq, Pi.neg_apply]
  split_ifs <;> ring_nf

lemma maxReal_neg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : maxReal (-f) n ω = maxReal f n ω := by
  simp [maxReal, maxFnN]

lemma squareReal_neg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : squareReal (-f) n ω = squareReal f n ω := by
  simp only [squareReal, dseq_neg, neg_sq]

lemma maxReal_sub_le (f g : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxReal (f-g) n ω ≤ maxReal f n ω + maxReal g n ω := by
  simpa only [sub_eq_add_neg, maxReal_neg] using maxReal_add_le f (-g) n ω

lemma squareReal_sub_le (f g : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    squareReal (f-g) n ω ≤ squareReal f n ω + squareReal g n ω := by
  simpa only [sub_eq_add_neg, squareReal_neg] using squareReal_add_le f (-g) n ω

end BurkholderDFI.ConvexPhi.Proof
-- End FiniteVariation

-- Begin PredictableMask

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

noncomputable def maskedIncrement (A : ℕ → Set Ω) (e : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  (A k).indicator (e k)

lemma maskedIncrement_adapted {A : ℕ → Set Ω} {e : ℕ → Ω → ℝ}
    (hA : ∀ k, MeasurableSet[ℱ k] (A k)) (he : StronglyAdapted ℱ e) :
    StronglyAdapted ℱ (maskedIncrement A e) := by
  intro k
  exact (he k).indicator (hA k)

omit [IsFiniteMeasure P] in
lemma maskedIncrement_integrable {A : ℕ → Set Ω} {e : ℕ → Ω → ℝ}
    (hA : ∀ k, MeasurableSet (A k)) (he : ∀ k, Integrable (e k) P) (k : ℕ) :
    Integrable (maskedIncrement A e k) P := (he k).indicator (hA k)

omit [IsFiniteMeasure P] in
lemma maskedIncrement_memLp {A : ℕ → Set Ω} {e : ℕ → Ω → ℝ}
    (hA : ∀ k, MeasurableSet (A k)) (he : ∀ k, MemLp (e k) 2 P) (k : ℕ) :
    MemLp (maskedIncrement A e k) 2 P := (he k).indicator (hA k)

omit [IsFiniteMeasure P] in
lemma maskedIncrement_condExp_zero {A : ℕ → Set Ω} {e : ℕ → Ω → ℝ}
    (hA : ∀ k, MeasurableSet[ℱ k] (A (k+1))) (he : ∀ k, Integrable (e k) P)
    (hz : ∀ k, P[e (k+1) | ℱ k] =ᵐ[P] 0) (k : ℕ) :
    P[maskedIncrement A e (k+1) | ℱ k] =ᵐ[P] 0 := by
  refine (condExp_indicator (he (k+1)) (hA k)).trans ?_
  filter_upwards [hz k] with ω hω
  by_cases h : ω ∈ A (k+1)
  · simp only [Set.indicator_of_mem h, hω]
  · simp only [Set.indicator_of_notMem h, Pi.zero_apply]

end BurkholderDFI.ConvexPhi.Proof
-- End PredictableMask

-- Begin SegmentAlgebra

namespace BurkholderDFI.ConvexPhi.Proof

noncomputable def segmentIncrement (a b : ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  if a < k ∧ k ≤ b then g k - g (k-1) else 0

lemma segment_sum {a b : ℕ} (hab : a ≤ b) (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, segmentIncrement a b g (k+1) =
      g (min b n) - g (min a n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hna : n < a
    · have hnb : n < b := lt_of_lt_of_le hna hab
      simp [segmentIncrement, show ¬ a < n+1 by omega,
        min_eq_right (by omega : n ≤ b), min_eq_right (by omega : n ≤ a),
        min_eq_right (by omega : n+1 ≤ b), min_eq_right (by omega : n+1 ≤ a)]
    · by_cases hnb : n < b
      · simp only [segmentIncrement, if_pos (show a < n+1 ∧ n+1 ≤ b by omega),
          Nat.add_sub_cancel, min_eq_right (by omega : n ≤ b),
          min_eq_right (by omega : n+1 ≤ b), min_eq_left (by omega : a ≤ n),
          min_eq_left (by omega : a ≤ n+1)]
        ring
      · simp [segmentIncrement, show ¬ n+1 ≤ b by omega,
          min_eq_left (by omega : b ≤ n), min_eq_left (by omega : b ≤ n+1),
          min_eq_left (by omega : a ≤ n), min_eq_left (by omega : a ≤ n+1)]

lemma segment_zero_of_reverse {a b : ℕ} (h : b ≤ a) (g : ℕ → ℝ) (k : ℕ) :
    segmentIncrement a b g k = 0 := by
  simp [segmentIncrement, show ¬ (a < k ∧ k ≤ b) by omega]

lemma segment_energy_le (a b : ℕ) (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, segmentIncrement a b g (k+1)^2 ≤
      ∑ k ∈ Finset.range n, (g (k+1)-g k)^2 := by
  apply Finset.sum_le_sum
  intro k _
  unfold segmentIncrement
  split_ifs
  · simp
  · simpa using sq_nonneg (g (k+1)-g k)

end BurkholderDFI.ConvexPhi.Proof
-- End SegmentAlgebra

-- Begin FiniteHit

namespace BurkholderDFI.ConvexPhi.Proof

noncomputable def finiteHit (p : ℕ → Prop) (N : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (show ∃ k, p k ∨ k = N from ⟨N, Or.inr rfl⟩)

lemma finiteHit_le (p : ℕ → Prop) (N : ℕ) : finiteHit p N ≤ N := by
  classical
  exact Nat.find_min' _ (Or.inr rfl)

lemma finiteHit_spec (p : ℕ → Prop) (N : ℕ) : p (finiteHit p N) ∨ finiteHit p N = N := by
  classical
  exact Nat.find_spec (show ∃ k, p k ∨ k = N from ⟨N, Or.inr rfl⟩)

lemma not_of_lt_finiteHit {p : ℕ → Prop} {N k : ℕ} (h : k < finiteHit p N) : ¬ p k := by
  classical
  intro hp
  exact Nat.not_lt_of_le (Nat.find_min' _ (Or.inl hp)) h

lemma finiteHit_le_of {p : ℕ → Prop} {N k : ℕ} (hp : p k) : finiteHit p N ≤ k := by
  classical
  exact Nat.find_min' _ (Or.inl hp)

lemma finiteHit_le_iff {p : ℕ → Prop} {N k : ℕ} (hk : k < N) :
    finiteHit p N ≤ k ↔ ∃ j ≤ k, p j := by
  classical
  constructor
  · intro h
    refine ⟨finiteHit p N, h, ?_⟩
    exact (finiteHit_spec p N).resolve_right (by omega)
  · rintro ⟨j, hj, hp⟩
    exact (finiteHit_le_of hp).trans hj

lemma finiteHit_eq_end {p : ℕ → Prop} {N : ℕ} (hp : ∀ k < N, ¬ p k) :
    finiteHit p N = N := by
  classical
  apply le_antisymm (finiteHit_le p N)
  by_contra h
  have hh : finiteHit p N < N := by omega
  exact hp _ hh ((finiteHit_spec p N).resolve_right (by omega))

open MeasureTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℕ mΩ}

lemma finiteHit_measurable_le {p : ℕ → Ω → Prop}
    (hp : ∀ k, MeasurableSet[ℱ k] {ω | p k ω}) (N k : ℕ) :
    MeasurableSet[ℱ k] {ω | finiteHit (fun j => p j ω) N ≤ k} := by
  classical
  by_cases hk : k < N
  · have he : {ω | finiteHit (fun j => p j ω) N ≤ k} =
        ⋃ j : ℕ, ⋃ (_ : j ≤ k), {ω | p j ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, finiteHit_le_iff hk]
      simp
    rw [he]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj =>
      ℱ.mono hj _ (hp j)
  · have he : {ω | finiteHit (fun j => p j ω) N ≤ k} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (finiteHit_le _ N).trans (by omega)
    rw [he]
    exact MeasurableSet.univ

end BurkholderDFI.ConvexPhi.Proof
-- End FiniteHit

-- Begin SegmentStochastic

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

noncomputable def ordinaryDiff (f : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  f k - f (k-1)

lemma ordinaryDiff_adapted {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (ordinaryDiff f) := by
  intro k
  exact (hf k).sub ((hf (k-1)).mono (ℱ.mono (Nat.sub_le k 1)))

omit [IsFiniteMeasure P] in
lemma ordinaryDiff_integrable {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (k : ℕ) :
    Integrable (ordinaryDiff f k) P := (hf.integrable k).sub (hf.integrable (k-1))

lemma ordinaryDiff_condExp_zero {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (k : ℕ) :
    P[ordinaryDiff f (k+1)|ℱ k] =ᵐ[P] 0 := by
  have he : ordinaryDiff f (k+1) = f (k+1)-f k := by simp [ordinaryDiff]
  rw [he]
  refine (condExp_sub (hf.integrable (k+1)) (hf.integrable k) (ℱ k)).trans ?_
  rw [condExp_of_stronglyMeasurable (ℱ.le k) (hf.stronglyAdapted k) (hf.integrable k)]
  filter_upwards [hf.2 k (k+1) k.le_succ] with ω hω
  simp only [Pi.sub_apply, hω, sub_self, Pi.zero_apply]

noncomputable def segmentEvents (a b : Ω → ℕ) (k : ℕ) : Set Ω :=
  {ω | a ω < k ∧ k ≤ b ω}

lemma segmentEvents_predictable {a b : Ω → ℕ}
    (ha : ∀ k, MeasurableSet[ℱ k] {ω | a ω ≤ k})
    (hb : ∀ k, MeasurableSet[ℱ k] {ω | b ω ≤ k}) (k : ℕ) :
    MeasurableSet[ℱ k] (segmentEvents a b (k+1)) := by
  have he : segmentEvents a b (k+1) = {ω | a ω ≤ k} ∩ {ω | b ω ≤ k}ᶜ := by
    ext ω
    simp only [segmentEvents, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    omega
  rw [he]
  exact (ha k).inter (hb k).compl

lemma segmentEvents_adapted {a b : Ω → ℕ}
    (ha : ∀ k, MeasurableSet[ℱ k] {ω | a ω ≤ k})
    (hb : ∀ k, MeasurableSet[ℱ k] {ω | b ω ≤ k}) (k : ℕ) :
    MeasurableSet[ℱ k] (segmentEvents a b k) := by
  cases k with
  | zero =>
    let : MeasurableSpace Ω := ℱ 0
    simpa only [segmentEvents, Nat.not_lt_zero, false_and, Set.ofPred_false] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  | succ k => exact ℱ.mono k.le_succ _ (segmentEvents_predictable ha hb k)

noncomputable def stochasticSegment (f : ℕ → Ω → ℝ) (a b : Ω → ℕ) : ℕ → Ω → ℝ :=
  maskedIncrement (segmentEvents a b) (ordinaryDiff f)

lemma stochasticSegment_condExp_zero {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    {a b : Ω → ℕ} (ha : ∀ k, MeasurableSet[ℱ k] {ω | a ω ≤ k})
    (hb : ∀ k, MeasurableSet[ℱ k] {ω | b ω ≤ k}) (k : ℕ) :
    P[stochasticSegment f a b (k+1)|ℱ k] =ᵐ[P] 0 :=
  maskedIncrement_condExp_zero (segmentEvents_predictable ha hb)
    (ordinaryDiff_integrable hf) (ordinaryDiff_condExp_zero hf) k

omit mΩ in
lemma stochasticSegment_apply (f : ℕ → Ω → ℝ) (a b : Ω → ℕ) (k : ℕ) (ω : Ω) :
    stochasticSegment f a b k ω = segmentIncrement (a ω) (b ω) (fun j => f j ω) k := by
  simp [stochasticSegment, maskedIncrement, segmentEvents, ordinaryDiff, segmentIncrement,
    Set.indicator_apply]

omit mΩ in
lemma stochasticSegment_sum (f : ℕ → Ω → ℝ) {a b : Ω → ℕ}
    (hab : ∀ ω, a ω ≤ b ω) (n : ℕ) (ω : Ω) :
    partialProcess (stochasticSegment f a b) n ω =
      f (min (b ω) n) ω - f (min (a ω) n) ω := by
  simp only [partialProcess, Finset.sum_apply, stochasticSegment_apply]
  exact segment_sum (hab ω) (fun j => f j ω) n

end BurkholderDFI.ConvexPhi.Proof
-- End SegmentStochastic

-- Begin SegmentEnergy

namespace BurkholderDFI.ConvexPhi.Proof

lemma sum_mask_interval {a b : ℕ} (hab : a ≤ b) (v : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, if a < k+1 ∧ k+1 ≤ b then v (k+1) else 0) =
      (∑ k ∈ Finset.range (min b n), v (k+1)) -
      ∑ k ∈ Finset.range (min a n), v (k+1) := by
  let G : ℕ → ℝ := fun j => ∑ k ∈ Finset.range j, v (k+1)
  have hi : ∀ k, segmentIncrement a b G (k+1) =
      if a < k+1 ∧ k+1 ≤ b then v (k+1) else 0 := by
    intro k
    unfold segmentIncrement
    split_ifs
    · simp [G, Finset.sum_range_succ]
    · rfl
  have h := segment_sum hab G n
  simp only [hi] at h
  exact h

lemma segment_energy_eq {a b : ℕ} (hab : a ≤ b) (g : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, segmentIncrement a b g (k+1)^2) =
      (∑ k ∈ Finset.range (min b n), (g (k+1)-g k)^2) -
      ∑ k ∈ Finset.range (min a n), (g (k+1)-g k)^2 := by
  have hi : ∀ k, segmentIncrement a b g (k+1)^2 =
      if a < k+1 ∧ k+1 ≤ b then (g (k+1)-g k)^2 else 0 := by
    intro k
    unfold segmentIncrement
    split_ifs <;> simp
  simp only [hi]
  have h := sum_mask_interval hab (fun j => (g j-g (j-1))^2) n
  simpa only [Nat.add_sub_cancel] using h

lemma segment_energy_le_end {a b : ℕ} (hab : a ≤ b) (g : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, segmentIncrement a b g (k+1)^2) ≤
      ∑ k ∈ Finset.range (min b n), (g (k+1)-g k)^2 := by
  rw [segment_energy_eq hab]
  exact sub_le_self _ (Finset.sum_nonneg fun k _ => sq_nonneg _)

end BurkholderDFI.ConvexPhi.Proof
-- End SegmentEnergy

-- Begin StopBounds

namespace BurkholderDFI.ConvexPhi.Proof

noncomputable def pathEnergy (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (g (k+1)-g k)^2

lemma pathEnergy_zero (g : ℕ → ℝ) : pathEnergy g 0 = 0 := by simp [pathEnergy]
lemma pathEnergy_succ (g : ℕ → ℝ) (n : ℕ) :
    pathEnergy g (n+1) = pathEnergy g n + (g (n+1)-g n)^2 := by
  simp [pathEnergy, Finset.sum_range_succ]
lemma pathEnergy_nonneg (g : ℕ → ℝ) (n : ℕ) : 0 ≤ pathEnergy g n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma pathEnergy_mono (g : ℕ → ℝ) : Monotone (pathEnergy g) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [pathEnergy_succ]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma jump_bound_before_hit (w : ℕ → ℝ) (b : ℝ) (N : ℕ) {k : ℕ}
    (hk : 0 < k) (hstop : k ≤ finiteHit (fun j => b < w (j+1)) N) : w k ≤ b := by
  have h := not_of_lt_finiteHit (p := fun j => b < w (j+1)) (k := k-1)
    (show k-1 < finiteHit (fun j => b < w (j+1)) N by omega)
  simpa only [Nat.sub_add_cancel hk] using le_of_not_gt h

lemma value_before_hit (g : ℕ → ℝ) (l : ℝ) (N : ℕ) {k : ℕ}
    (hk : k < finiteHit (fun j => l < |g j|) N) : |g k| ≤ l :=
  le_of_not_gt (not_of_lt_finiteHit hk)

lemma value_at_stopped_bound (g : ℕ → ℝ) (w : ℕ → ℝ) (N : ℕ)
    {l b : ℝ} (hl : 0 ≤ l) (hb : 0 ≤ b) (hg0 : g 0 = 0)
    (hinc : ∀ k, 0 < k → k ≤ N → |g k-g (k-1)| ≤ w k)
    {k : ℕ} (hkM : k ≤ finiteHit (fun j => l < |g j|) N)
    (hkw : k ≤ finiteHit (fun j => b < w (j+1)) N) : |g k| ≤ l+b := by
  by_cases hk0 : k = 0
  · subst k; simpa [hg0] using add_nonneg hl hb
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hp := value_before_hit g l N (k := k-1) (by omega)
  have hi := (hinc k hk (hkM.trans (finiteHit_le _ N))).trans
    (jump_bound_before_hit w b N hk hkw)
  have htri := abs_add_le (g k-g (k-1)) (g (k-1))
  have hid : g k-g (k-1)+g (k-1) = g k := by ring
  rw [hid] at htri
  linarith

lemma energy_at_stopped_bound (g : ℕ → ℝ) (w : ℕ → ℝ) (N : ℕ)
    {l b : ℝ} (hb : 0 ≤ b)
    (hinc : ∀ k, 0 < k → k ≤ N → |g k-g (k-1)| ≤ w k)
    {k : ℕ} (hkS : k ≤ finiteHit (fun j => l^2 < pathEnergy g j) N)
    (hkw : k ≤ finiteHit (fun j => b < w (j+1)) N) : pathEnergy g k ≤ l^2+b^2 := by
  cases k with
  | zero => simpa [pathEnergy] using add_nonneg (sq_nonneg l) (sq_nonneg b)
  | succ k =>
    have hp : pathEnergy g k ≤ l^2 :=
      le_of_not_gt (not_of_lt_finiteHit (N := N) (p := fun j => l^2 < pathEnergy g j) (by omega))
    have hi := (hinc (k+1) (by omega) (hkS.trans (finiteHit_le _ N))).trans
      (jump_bound_before_hit w b N (by omega) hkw)
    simp only [Nat.add_sub_cancel] at hi
    rw [pathEnergy_succ]
    nlinarith [sq_abs (g (k+1)-g k), abs_nonneg (g (k+1)-g k)]

end BurkholderDFI.ConvexPhi.Proof
-- End StopBounds

-- Begin StopMeasurable

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℕ mΩ}

lemma pathEnergy_adapted {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (fun n ω => pathEnergy (fun j => f j ω) n) := by
  intro n
  have h : StronglyMeasurable[ℱ n] (∑ k ∈ Finset.range n, fun ω => (f (k+1) ω-f k ω)^2) := by
    apply Finset.stronglyMeasurable_sum
    intro k hk
    have hk' : k+1 ≤ n := Finset.mem_range.mp hk
    exact (((hf (k+1)).mono (ℱ.mono hk')).sub
      ((hf k).mono (ℱ.mono (by omega)))).pow 2
  have he : (fun ω => pathEnergy (fun j => f j ω) n) =
      ∑ k ∈ Finset.range n, (fun ω => (f (k+1) ω-f k ω)^2) := by
    funext ω
    simp [pathEnergy]
  change StronglyMeasurable[ℱ n] (fun ω => pathEnergy (fun j => f j ω) n)
  rw [he]
  exact h

lemma stopping_min_measurable {a b : Ω → ℕ}
    (ha : ∀ k, MeasurableSet[ℱ k] {ω | a ω ≤ k})
    (hb : ∀ k, MeasurableSet[ℱ k] {ω | b ω ≤ k}) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | min (a ω) (b ω) ≤ k} := by
  have he : {ω | min (a ω) (b ω) ≤ k} = {ω | a ω ≤ k} ∪ {ω | b ω ≤ k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, min_le_iff]
  rw [he]
  exact (ha k).union (hb k)

lemma valueHit_measurable {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f)
    (l : ℝ) (N k : ℕ) :
    MeasurableSet[ℱ k] {ω | finiteHit (fun j => l < |f j ω|) N ≤ k} := by
  apply finiteHit_measurable_le
  intro j
  let : MeasurableSpace Ω := ℱ j
  exact measurableSet_lt measurable_const (hf j).measurable.abs

lemma energyHit_measurable {f : ℕ → Ω → ℝ} (hf : StronglyAdapted ℱ f)
    (l : ℝ) (N k : ℕ) :
    MeasurableSet[ℱ k] {ω | finiteHit (fun j => l^2 < pathEnergy (fun i => f i ω) j) N ≤ k} := by
  apply finiteHit_measurable_le
  intro j
  let : MeasurableSpace Ω := ℱ j
  exact measurableSet_lt measurable_const (pathEnergy_adapted (mΩ := mΩ) hf j).measurable

lemma jumpHit_measurable {w : ℕ → Ω → ℝ}
    (hw : ∀ k, StronglyMeasurable[ℱ k] (w (k+1))) (l : ℝ) (N k : ℕ) :
    MeasurableSet[ℱ k] {ω | finiteHit (fun j => l < w (j+1) ω) N ≤ k} := by
  apply finiteHit_measurable_le
  intro j
  let : MeasurableSpace Ω := ℱ j
  exact measurableSet_lt measurable_const (hw j).measurable

end BurkholderDFI.ConvexPhi.Proof
-- End StopMeasurable

-- Begin NativeNormBridge

open MeasureTheory ProbabilityTheory
open BurkholderDFI.SquareFnLp

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*}

lemma sum_Icc_one_eq_range (v : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, v k = ∑ k ∈ Finset.range n, v (k+1) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

lemma runningAbs_eq_maxReal (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    runningAbs (fun k => f k ω) n = maxReal f n ω := by
  apply le_antisymm
  · exact runningAbs_le (maxReal_nonneg f n ω)
      (fun k hk hkn => abs_le_maxReal f (Finset.mem_Icc.mpr ⟨hk,hkn⟩) ω)
  · exact maxReal_le f n ω (runningAbs_nonneg _ n)
      (fun k hk => abs_le_runningAbs (fun k => f k ω) (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)

lemma ordinaryDiff_eq_dseq (f : ℕ → Ω → ℝ) (hzero : f 0 = 0) (k : ℕ) :
    ordinaryDiff f k = dseq f k := by
  funext ω
  by_cases h0 : k=0
  · subst k; simp [ordinaryDiff,dseq]
  by_cases h1 : k=1
  · subst k; simp [ordinaryDiff,dseq,hzero]
  · simp [ordinaryDiff,dseq,h0,h1]

lemma pathEnergy_eq_squareReal_sq (f : ℕ → Ω → ℝ) (hzero : f 0 = 0) (n : ℕ) (ω : Ω) :
    pathEnergy (fun k => f k ω) n = squareReal f n ω^2 := by
  rw [squareReal_sq, sum_Icc_one_eq_range]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrFun (ordinaryDiff_eq_dseq f hzero (k+1)) ω
  simpa only [ordinaryDiff, Pi.sub_apply, Nat.add_sub_cancel, h] using congrArg (fun x : ℝ => x^2) h

variable [mΩ : MeasurableSpace Ω]

lemma maxReal_measurable {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f (k+1))) (n : ℕ) :
    Measurable (maxReal f n) := by
  have h : ∀ n, Measurable (fun ω => runningAbs (fun k => f k ω) n) := by
    intro n
    induction n with
    | zero => exact measurable_const
    | succ n ih => exact ih.max (hf n).abs
  simpa only [runningAbs_eq_maxReal] using h n

lemma squareReal_measurable {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k)) (n : ℕ) :
    Measurable (squareReal f n) := by
  have hd : ∀ k, Measurable (dseq f k) := by
    intro k
    by_cases h0 : k=0
    · subst k; rw [native_dseq_zero]; exact measurable_const
    by_cases h1 : k=1
    · subst k; rw [native_dseq_one]; exact hf 1
    · have he : dseq f k = f k - f (k-1) := by ext ω; simp [dseq,h0,h1]
      rw [he]
      exact (hf k).sub (hf (k-1))
  exact (Finset.measurable_sum _ (fun k _ => (hd k).pow_const 2)).sqrt

end BurkholderDFI.ConvexPhi.Proof
-- End NativeNormBridge

-- Begin DavisOrlicz

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp

lemma davis_variation_orlicz_uniform (c : ℝ≥0) : ∃ L : ℝ≥0, 0 < L ∧
    ∀ (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
    ∀ (Φ : ℝ≥0∞ → ℝ≥0∞), IsPhi Φ c → IsConvexPhi Φ → ∀ n,
      phiMoment P Φ (variationReal (davisBad ℱ P f) n) ≤ L*phiMoment P Φ (maxReal (dseq f) n) := by
  obtain ⟨K, _hK, hcomp⟩ := compensator_uniform c
  refine ⟨1+c^2*(1+K), by positivity, ?_⟩
  intro Ω mΩ P hP ℱ f hf Φ hΦ hcv n
  let z : ℕ → Ω → ℝ := fun k ω => |davisLarge f (k+1) ω|
  let Z : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, z k ω
  let W : Ω → ℝ := compensator ℱ P z n
  have hz (k : ℕ) : Measurable (z k) :=
    ((davisLarge_adapted hf.stronglyAdapted (k+1)).mono (ℱ.le _)).measurable.abs
  have hzi (k : ℕ) : Integrable (z k) P := (davisLarge_integrable hf (k+1)).abs
  have hz0 (k : ℕ) (ω : Ω) : 0 ≤ z k ω := abs_nonneg _
  have hZm : Measurable Z := Finset.measurable_sum _ fun k _ => hz k
  have hWm : Measurable W := Finset.measurable_sum _ fun k _ =>
    stronglyMeasurable_condExp.measurable.mono (ℱ.le k) le_rfl
  have hW : phiMoment P Φ W ≤ K*phiMoment P Φ Z := hcomp Ω P ℱ Φ hΦ hcv z hz hzi hz0 n
  have hZ : phiMoment P Φ Z ≤ c*phiMoment P Φ (maxReal (dseq f) n) := by
    have hmono : Z ≤ᵐ[P] (fun ω => 2*maxReal (dseq f) n ω) := ae_of_all _ fun ω => by
      simpa only [runningAbs_eq_maxReal] using davisLarge_sum_bound f n ω
    have hs := phiMoment_scale_pow (P := P) hΦ (maxReal (dseq f) n) 1
    simp only [pow_one] at hs
    exact (phiMoment_mono hΦ hmono).trans hs
  have hH := phiMoment_add_bound hΦ hZm hWm (davisBad_variation_bound hf n)
  change phiMoment P Φ (variationReal (davisBad ℱ P f) n) ≤ c*(phiMoment P Φ Z+phiMoment P Φ W) at hH
  calc
    _ ≤ c*(phiMoment P Φ Z+K*phiMoment P Φ Z) := hH.trans (mul_le_mul' le_rfl (add_le_add le_rfl hW))
    _ = ((c:ℝ≥0∞)*(1+K))*phiMoment P Φ Z := by ring
    _ ≤ ((c:ℝ≥0∞)*(1+K))*(c*phiMoment P Φ (maxReal (dseq f) n)) := mul_le_mul' le_rfl hZ
    _ = ((c:ℝ≥0∞)^2*(1+K))*phiMoment P Φ (maxReal (dseq f) n) := by ring
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      push_cast
      exact le_add_of_nonneg_left zero_le

end BurkholderDFI.ConvexPhi.Proof
-- End DavisOrlicz

-- Begin OrliczAlgebra

namespace BurkholderDFI.ConvexPhi.Proof
open scoped ENNReal NNReal

lemma orlicz_transfer {X Y Z T H D W c K L b : ℝ≥0∞}
    (hX : X ≤ c*(Y+H)) (hY : Y ≤ K*(Z+W)) (hZ : Z ≤ c*(T+H))
    (hH : H ≤ L*D) (hW : W ≤ c^2*D) (hD : D ≤ b*T) :
    X ≤ (c*(K*(c*(1+L*b)+c^2*b)+L*b))*T := by
  have hH' := hH.trans (mul_le_mul' le_rfl hD)
  have hW' := hW.trans (mul_le_mul' le_rfl hD)
  have hZ' := hZ.trans (mul_le_mul' le_rfl (add_le_add le_rfl hH'))
  have hY' := hY.trans (mul_le_mul' le_rfl (add_le_add hZ' hW'))
  calc
    X ≤ c*(K*(c*(T+L*(b*T))+c^2*(b*T))+L*(b*T)) :=
      hX.trans (mul_le_mul' le_rfl (add_le_add hY' hH'))
    _ = _ := by ring

noncomputable def comparisonConstant (c K L : ℝ≥0) : ℝ≥0 :=
  1+c*(K*(c*(1+L*c)+c^2*c)+L*c)+c*(K*(c*(1+L)+c^2)+L)

lemma comparisonConstant_pos (c K L : ℝ≥0) : 0 < comparisonConstant c K L := by
  unfold comparisonConstant
  positivity

lemma orlicz_pair_transfer {A B U V H D W : ℝ≥0∞} (c K L : ℝ≥0)
    (hA : A ≤ c*(U+H)) (hB : B ≤ c*(V+H))
    (hU : U ≤ c*(A+H)) (hV : V ≤ c*(B+H))
    (hUV : U ≤ K*(V+W)) (hVU : V ≤ K*(U+W))
    (hH : H ≤ L*D) (hW : W ≤ (c:ℝ≥0∞)^2*D)
    (hDA : D ≤ A) (hDB : D ≤ c*B) :
    A ≤ comparisonConstant c K L*B ∧ B ≤ comparisonConstant c K L*A := by
  constructor
  · refine (orlicz_transfer hA hUV hV hH hW hDB).trans (mul_le_mul' ?_ le_rfl)
    simp only [comparisonConstant]
    push_cast
    exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
  · have hd : D ≤ 1*A := by simpa using hDA
    have h := orlicz_transfer hB hVU hU hH hW hd
    simp only [mul_one] at h
    refine h.trans (mul_le_mul' ?_ le_rfl)
    simp only [comparisonConstant]
    push_cast
    exact le_add_of_nonneg_left zero_le

end BurkholderDFI.ConvexPhi.Proof
-- End OrliczAlgebra

-- Begin FiniteOrlicz

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma finite_orlicz_comparison (hf : Martingale f ℱ P) (hΦ : IsPhi Φ c)
    (K L : ℝ≥0) (n : ℕ)
    (hH : phiMoment P Φ (variationReal (davisBad ℱ P f) n) ≤ L*phiMoment P Φ (maxReal (dseq f) n))
    (hSG : phiMoment P Φ (squareReal (davisGood ℱ P f) n) ≤
      K*(phiMoment P Φ (maxReal (davisGood ℱ P f) n)+phiMoment P Φ (fun ω => 4*maxReal (dseq f) n ω)))
    (hMG : phiMoment P Φ (maxReal (davisGood ℱ P f) n) ≤
      K*(phiMoment P Φ (squareReal (davisGood ℱ P f) n)+phiMoment P Φ (fun ω => 4*maxReal (dseq f) n ω))) :
    phiMoment P Φ (squareReal f n) ≤ comparisonConstant c K L*phiMoment P Φ (maxReal f n) ∧
    phiMoment P Φ (maxReal f n) ≤ comparisonConstant c K L*phiMoment P Φ (squareReal f n) := by
  let g := davisGood ℱ P f
  let h := davisBad ℱ P f
  have hg : Martingale g ℱ P := davisGood_martingale hf
  have hh : Martingale h ℱ P := davisBad_martingale hf
  have hfm (k : ℕ) : Measurable (f k) := ((hf.stronglyAdapted k).mono (ℱ.le k)).measurable
  have hgm (k : ℕ) : Measurable (g k) := ((hg.stronglyAdapted k).mono (ℱ.le k)).measurable
  have hhm : Measurable (variationReal h n) := by
    apply Finset.measurable_sum
    intro k _
    exact ((dseq_adapted hh.stronglyAdapted (k+1)).mono (ℱ.le _)).measurable.abs
  have hfg : f = g+h := by ext k ω; simp [g,h,davisBad]
  have hgf : g = f-h := by ext k ω; simp [g,h,davisBad]
  have hA : phiMoment P Φ (squareReal f n) ≤
      c*(phiMoment P Φ (squareReal g n)+phiMoment P Φ (variationReal h n)) := by
    apply phiMoment_add_bound hΦ (squareReal_measurable hgm n) hhm
    exact ae_of_all _ fun ω => by
      calc
        squareReal f n ω = squareReal (g+h) n ω := by rw [← hfg]
        _ ≤ squareReal g n ω+squareReal h n ω := squareReal_add_le _ _ _ _
        _ ≤ _ := add_le_add le_rfl (squareReal_le_variationReal h n ω)
  have hB : phiMoment P Φ (maxReal f n) ≤
      c*(phiMoment P Φ (maxReal g n)+phiMoment P Φ (variationReal h n)) := by
    apply phiMoment_add_bound hΦ (maxReal_measurable (fun k => hgm (k+1)) n) hhm
    exact ae_of_all _ fun ω => by
      calc
        maxReal f n ω = maxReal (g+h) n ω := by rw [← hfg]
        _ ≤ maxReal g n ω+maxReal h n ω := maxReal_add_le _ _ _ _
        _ ≤ _ := add_le_add le_rfl (maxReal_le_variationReal h n ω)
  have hU : phiMoment P Φ (squareReal g n) ≤
      c*(phiMoment P Φ (squareReal f n)+phiMoment P Φ (variationReal h n)) := by
    apply phiMoment_add_bound hΦ (squareReal_measurable hfm n) hhm
    exact ae_of_all _ fun ω => by
      calc
        squareReal g n ω = squareReal (f-h) n ω := by rw [← hgf]
        _ ≤ squareReal f n ω+squareReal h n ω := squareReal_sub_le _ _ _ _
        _ ≤ _ := add_le_add le_rfl (squareReal_le_variationReal h n ω)
  have hV : phiMoment P Φ (maxReal g n) ≤
      c*(phiMoment P Φ (maxReal f n)+phiMoment P Φ (variationReal h n)) := by
    apply phiMoment_add_bound hΦ (maxReal_measurable (fun k => hfm (k+1)) n) hhm
    exact ae_of_all _ fun ω => by
      calc
        maxReal g n ω = maxReal (f-h) n ω := by rw [← hgf]
        _ ≤ maxReal f n ω+maxReal h n ω := maxReal_sub_le _ _ _ _
        _ ≤ _ := add_le_add le_rfl (maxReal_le_variationReal h n ω)
  have hW : phiMoment P Φ (fun ω => 4*maxReal (dseq f) n ω) ≤ (c:ℝ≥0∞)^2*phiMoment P Φ (maxReal (dseq f) n) := by
    simpa only [show (2:ℝ)^2=4 by norm_num] using phiMoment_scale_pow hΦ (maxReal (dseq f) n) 2
  have hDA := phiMoment_mono (P := P) hΦ (ae_of_all P (maxReal_dseq_le_squareReal f n))
  have hDB : phiMoment P Φ (maxReal (dseq f) n) ≤ c*phiMoment P Φ (maxReal f n) := by
    have h₁ := phiMoment_mono (P := P) hΦ (ae_of_all P (maxReal_dseq_le_maxReal f n))
    have h₂ := phiMoment_scale_pow (P := P) hΦ (maxReal f n) 1
    exact h₁.trans (by simpa only [pow_one] using h₂)
  exact orlicz_pair_transfer c K L hA hB hU hV hSG hMG hH hW hDA hDB

end BurkholderDFI.ConvexPhi.Proof
-- End FiniteOrlicz

-- Begin SquareSegment

namespace BurkholderDFI.ConvexPhi.Proof

noncomputable def squareStop (g w : ℕ → ℝ) (_l b : ℝ) (N : ℕ) : ℕ :=
  min (finiteHit (fun j => b < |g j|) N) (finiteHit (fun j => b < w (j+1)) N)

noncomputable def squareStart (g w : ℕ → ℝ) (l b : ℝ) (N : ℕ) : ℕ :=
  min (finiteHit (fun j => l^2 < pathEnergy g j) N) (squareStop g w l b N)

lemma squareStart_le_stop (g w : ℕ → ℝ) (l b : ℝ) (N : ℕ) :
    squareStart g w l b N ≤ squareStop g w l b N := min_le_right _ _
lemma squareStop_le_end (g w : ℕ → ℝ) (l b : ℝ) (N : ℕ) :
    squareStop g w l b N ≤ N := (min_le_left _ _).trans (finiteHit_le _ N)

lemma squareSegment_endpoint_bound (g w : ℕ → ℝ) (N : ℕ) {l b : ℝ}
    (hb : 0 ≤ b) (hg0 : g 0 = 0)
    (hi : ∀ k, 0 < k → k ≤ N → |g k-g (k-1)| ≤ w k) :
    |∑ k ∈ Finset.range N, segmentIncrement (squareStart g w l b N)
      (squareStop g w l b N) g (k+1)| ≤ 4*b := by
  rw [segment_sum (squareStart_le_stop g w l b N),
    min_eq_left (squareStop_le_end g w l b N),
    min_eq_left ((squareStart_le_stop g w l b N).trans (squareStop_le_end g w l b N))]
  have h1 := value_at_stopped_bound g w N hb hb hg0 hi
    (k := squareStop g w l b N) (min_le_left _ _) (min_le_right _ _)
  have h2 := value_at_stopped_bound g w N hb hb hg0 hi
    (k := squareStart g w l b N)
    ((squareStart_le_stop g w l b N).trans (min_le_left _ _))
    ((squareStart_le_stop g w l b N).trans (min_le_right _ _))
  exact (abs_sub _ _).trans (by linarith)

lemma squareSegment_zero (g w : ℕ → ℝ) (N : ℕ) {l b : ℝ}
    (hE : pathEnergy g N ≤ l^2) :
    ∑ k ∈ Finset.range N, segmentIncrement (squareStart g w l b N)
      (squareStop g w l b N) g (k+1) = 0 := by
  have hm : finiteHit (fun j => l^2 < pathEnergy g j) N = N :=
    finiteHit_eq_end (fun k hk => not_lt_of_ge ((pathEnergy_mono g hk.le).trans hE))
  have hs : squareStart g w l b N = squareStop g w l b N := by
    rw [squareStart, hm, min_eq_right (squareStop_le_end g w l b N)]
  simp only [hs, segment_zero_of_reverse le_rfl, Finset.sum_const_zero]

lemma squareSegment_target_energy (g w : ℕ → ℝ) (N : ℕ) {l b : ℝ}
    (hl : 0 < l) (hb : 0 ≤ b) (hbl : b ≤ l) (hg0 : g 0 = 0)
    (hi : ∀ k, 0 < k → k ≤ N → |g k-g (k-1)| ≤ w k)
    (hM : ∀ k, 0 < k → k ≤ N → |g k| ≤ b)
    (hw : ∀ k, 0 < k → k ≤ N → w k ≤ b)
    (hE : 4*l^2 < pathEnergy g N) :
    l^2 ≤ ∑ k ∈ Finset.range N, segmentIncrement (squareStart g w l b N)
      (squareStop g w l b N) g (k+1)^2 := by
  have htM : finiteHit (fun j => b < |g j|) N = N := by
    apply finiteHit_eq_end
    intro k hk
    by_cases hk0 : k=0
    · subst k; simpa [hg0] using not_lt_of_ge hb
    · exact not_lt_of_ge (hM k (Nat.pos_of_ne_zero hk0) hk.le)
  have htw : finiteHit (fun j => b < w (j+1)) N = N :=
    finiteHit_eq_end (fun k hk => not_lt_of_ge (hw (k+1) (by omega) (by omega)))
  have ht : squareStop g w l b N = N := by simp [squareStop, htM, htw]
  have ha : squareStart g w l b N = finiteHit (fun j => l^2 < pathEnergy g j) N := by
    rw [squareStart, ht, min_eq_left (finiteHit_le _ N)]
  have he := energy_at_stopped_bound g w N hb hi (k := finiteHit (fun j => l^2 < pathEnergy g j) N)
    le_rfl (by rw [htw]; exact finiteHit_le _ N)
  rw [segment_energy_eq (squareStart_le_stop g w l b N), ht, min_self, ha,
    min_eq_left (finiteHit_le _ N)]
  change l^2 ≤ pathEnergy g N - pathEnergy g (finiteHit (fun j => l^2 < pathEnergy g j) N)
  nlinarith

end BurkholderDFI.ConvexPhi.Proof
-- End SquareSegment

-- Begin SegmentL2

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

lemma stochasticSegment_memLp {f w : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    {a b : Ω → ℕ} (ha : ∀ k, MeasurableSet[ℱ k] {ω | a ω ≤ k})
    (hb : ∀ k, MeasurableSet[ℱ k] {ω | b ω ≤ k}) {B : ℝ} (hB : 0 ≤ B) (N : ℕ)
    (hbw : ∀ ω, b ω ≤ finiteHit (fun j => B < w (j+1) ω) N)
    (hi : ∀ k, ∀ᵐ ω ∂P, |ordinaryDiff f (k+1) ω| ≤ w (k+1) ω) (k : ℕ) :
    MemLp (stochasticSegment f a b k) 2 P := by
  have hm := maskedIncrement_adapted (segmentEvents_adapted ha hb)
    (ordinaryDiff_adapted hf.stronglyAdapted) k
  apply MemLp.of_bound (hm.mono (ℱ.le k)).aestronglyMeasurable B
  cases k with
  | zero =>
    exact Filter.Eventually.of_forall fun ω => by
      simp [maskedIncrement, segmentEvents, hB]
  | succ k =>
    filter_upwards [hi k] with ω hω
    rw [Real.norm_eq_abs]
    change |stochasticSegment f a b (k+1) ω| ≤ B
    rw [stochasticSegment_apply]
    unfold segmentIncrement
    by_cases h : a ω < k+1 ∧ k+1 ≤ b ω
    · rw [if_pos h]
      have hj := jump_bound_before_hit (fun j => w j ω) B N (by omega : 0 < k+1)
        (h.2.trans (hbw ω))
      simpa only [ordinaryDiff, Pi.sub_apply, Nat.add_sub_cancel] using hω.trans hj
    · rw [if_neg h, abs_zero]
      exact hB

end BurkholderDFI.ConvexPhi.Proof
-- End SegmentL2

-- Begin EventEnergy

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

lemma integral_sq_le_event {X : Ω → ℝ} (hX : MemLp X 2 P) {A : Set Ω}
    (hA : MeasurableSet A) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, |X ω| ≤ A.indicator (fun _ => b) ω) :
    (∫ ω, X ω ^ 2 ∂P) ≤ b^2 * P.real A := by
  have hi : Integrable (A.indicator (fun _ : Ω => b^2)) P := integrable_const _ |>.indicator hA
  have hle : (fun ω => X ω^2) ≤ᵐ[P] A.indicator (fun _ => b^2) := by
    filter_upwards [hbound] with ω hω
    by_cases ha : ω ∈ A
    · simp only [Set.indicator_of_mem ha] at hω ⊢
      nlinarith [sq_abs (X ω), abs_nonneg (X ω)]
    · simp only [Set.indicator_of_notMem ha] at hω ⊢
      have hz : X ω = 0 := abs_nonpos_iff.mp hω
      simp [hz]
  calc
    _ ≤ ∫ ω, A.indicator (fun _ => b^2) ω ∂P := integral_mono_ae hX.integrable_sq hi hle
    _ = b^2 * P.real A := by rw [integral_indicator hA, setIntegral_const]; simp [mul_comm]

lemma event_le_integral_sq {X : Ω → ℝ} (hX : MemLp X 2 P) {A : Set Ω}
    (hA : MeasurableSet A) {b : ℝ}
    (hbound : ∀ᵐ ω ∂P, A.indicator (fun _ => b) ω ≤ X ω ^ 2) :
    b * P.real A ≤ ∫ ω, X ω ^ 2 ∂P := by
  have hi : Integrable (A.indicator (fun _ : Ω => b)) P := integrable_const _ |>.indicator hA
  calc
    _ = ∫ ω, A.indicator (fun _ => b) ω ∂P := by
      rw [integral_indicator hA, setIntegral_const]; simp [mul_comm]
    _ ≤ _ := integral_mono_ae hi hX.integrable_sq hbound

lemma event_le_integral_energy {e : ℕ → Ω → ℝ} (he : ∀ k, MemLp (e k) 2 P)
    (n : ℕ) {A : Set Ω} (hA : MeasurableSet A) {b : ℝ}
    (hbound : ∀ᵐ ω ∂P, A.indicator (fun _ => b) ω ≤
      ∑ k ∈ Finset.range n, e (k+1) ω ^ 2) :
    b * P.real A ≤ ∑ k ∈ Finset.range n, ∫ ω, e (k+1) ω ^ 2 ∂P := by
  have hi : Integrable (A.indicator (fun _ : Ω => b)) P := integrable_const _ |>.indicator hA
  have hs : Integrable (fun ω => ∑ k ∈ Finset.range n, e (k+1) ω ^ 2) P :=
    integrable_finsetSum _ (fun k _ => (he (k+1)).integrable_sq)
  calc
    _ = ∫ ω, A.indicator (fun _ => b) ω ∂P := by
      rw [integral_indicator hA, setIntegral_const]; simp [mul_comm]
    _ ≤ ∫ ω, ∑ k ∈ Finset.range n, e (k+1) ω ^ 2 ∂P := integral_mono_ae hi hs hbound
    _ = _ := integral_finsetSum _ (fun k _ => (he (k+1)).integrable_sq)

end BurkholderDFI.ConvexPhi.Proof
-- End EventEnergy

-- Begin SquareProbability

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

lemma square_segment_probability {f w : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    (hw : ∀ k, StronglyMeasurable[ℱ k] (w (k+1)))
    (hi : ∀ k, ∀ᵐ ω ∂P, |ordinaryDiff f (k+1) ω| ≤ w (k+1) ω)
    (hzero : f 0 = 0) (N : ℕ) {l b : ℝ} (hl : 0 < l) (hb : 0 ≤ b) (hbl : b ≤ l)
    {E : Set Ω} (hE : MeasurableSet E)
    (htarget : ∀ ω ∈ E, 4*l^2 < pathEnergy (fun j => f j ω) N ∧
      (∀ k, 0 < k → k ≤ N → |f k ω| ≤ b) ∧
      (∀ k, 0 < k → k ≤ N → w k ω ≤ b)) :
    l^2 * P.real E ≤ (4*b)^2 * P.real {ω | l^2 < pathEnergy (fun j => f j ω) N} := by
  let a : Ω → ℕ := fun ω => squareStart (fun j => f j ω) (fun j => w j ω) l b N
  let z : Ω → ℕ := fun ω => squareStop (fun j => f j ω) (fun j => w j ω) l b N
  let e := stochasticSegment f a z
  have hzM : ∀ k, MeasurableSet[ℱ k] {ω | z ω ≤ k} :=
    stopping_min_measurable (valueHit_measurable hf.stronglyAdapted b N) (jumpHit_measurable hw b N)
  have haM : ∀ k, MeasurableSet[ℱ k] {ω | a ω ≤ k} :=
    stopping_min_measurable (energyHit_measurable hf.stronglyAdapted l N) hzM
  have h2 : ∀ k, MemLp (e k) 2 P := stochasticSegment_memLp hf haM hzM hb N
    (fun _ => min_le_right _ _) hi
  have had : StronglyAdapted ℱ e := maskedIncrement_adapted (segmentEvents_adapted haM hzM)
    (ordinaryDiff_adapted hf.stronglyAdapted)
  have hmean := stochasticSegment_condExp_zero hf haM hzM
  have hA : MeasurableSet {ω | l^2 < pathEnergy (fun j => f j ω) N} :=
    measurableSet_lt measurable_const ((pathEnergy_adapted hf.stronglyAdapted N).mono (ℱ.le N)).measurable
  have hp : ∀ᵐ ω ∂P, ∀ k, 0 < k → k ≤ N → |f k ω-f (k-1) ω| ≤ w k ω := by
    filter_upwards [ae_all_iff.mpr hi] with ω hω
    intro k hk _
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact hω j
  have hlow : ∀ᵐ ω ∂P, E.indicator (fun _ => l^2) ω ≤ ∑ k ∈ Finset.range N, e (k+1) ω^2 := by
    filter_upwards [hp] with ω hω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      have ht := htarget ω he
      have h := squareSegment_target_energy (fun j => f j ω) (fun j => w j ω) N hl hb hbl
        (congrFun hzero ω) hω ht.2.1 ht.2.2 ht.1
      simpa only [e, stochasticSegment_apply, a, z] using h
    · rw [Set.indicator_of_notMem he]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hupp : ∀ᵐ ω ∂P, |partialProcess e N ω| ≤
      {ω | l^2 < pathEnergy (fun j => f j ω) N}.indicator (fun _ => 4*b) ω := by
    filter_upwards [hp] with ω hω
    simp only [partialProcess, Finset.sum_apply, e, stochasticSegment_apply, a, z]
    by_cases he : l^2 < pathEnergy (fun j => f j ω) N
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, he, if_true]
      exact squareSegment_endpoint_bound _ _ N hb (congrFun hzero ω) hω
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, he, if_false]
      rw [squareSegment_zero _ _ N (le_of_not_gt he), abs_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range N, ∫ ω, e (k+1) ω^2 ∂P := event_le_integral_energy h2 N hE hlow
    _ = ∫ ω, partialProcess e N ω^2 ∂P := (partialProcess_energy had h2 hmean N).symm
    _ ≤ _ := integral_sq_le_event (partialProcess_memLp h2 N) hA (by positivity) hupp

end BurkholderDFI.ConvexPhi.Proof
-- End SquareProbability

-- Begin TailUnion

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BurkholderDFI.ConvexPhi.Proof
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma tail_union_bound (U V W : Ω → ℝ) (δ t : ℝ) (q : ℝ≥0∞)
    (h : P {ω | 2*t < V ω ∧ U ω ≤ δ*t ∧ W ω ≤ δ*t} ≤ q * P {ω | t < V ω}) :
    P {ω | 2*t < V ω} ≤ P {ω | δ*t < U ω} + P {ω | δ*t < W ω} + q * P {ω | t < V ω} := by
  let E := {ω | 2*t < V ω ∧ U ω ≤ δ*t ∧ W ω ≤ δ*t}
  have hs : {ω | 2*t < V ω} ⊆ ({ω | δ*t < U ω} ∪ {ω | δ*t < W ω}) ∪ E := by
    intro ω hω
    by_cases hu : δ*t < U ω
    · exact Or.inl (Or.inl hu)
    by_cases hw : δ*t < W ω
    · exact Or.inl (Or.inr hw)
    · exact Or.inr ⟨hω, le_of_not_gt hu, le_of_not_gt hw⟩
  calc
    _ ≤ P (({ω | δ*t < U ω} ∪ {ω | δ*t < W ω}) ∪ E) := measure_mono hs
    _ ≤ P ({ω | δ*t < U ω} ∪ {ω | δ*t < W ω}) + P E := measure_union_le _ _
    _ ≤ (P {ω | δ*t < U ω} + P {ω | δ*t < W ω}) + P E :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ _ := add_le_add le_rfl h

lemma measure_le_of_real [IsFiniteMeasure P] {E A : Set Ω} {q : ℝ} (hq : 0 ≤ q)
    (h : P.real E ≤ q * P.real A) : P E ≤ ENNReal.ofReal q * P A := by
  have hh := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul hq, ofReal_measureReal (measure_ne_top P E),
    ofReal_measureReal (measure_ne_top P A)] at hh
  exact hh

end BurkholderDFI.ConvexPhi.Proof
-- End TailUnion

-- Begin SquareTail

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BurkholderDFI.ConvexPhi.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

lemma square_goodLambda {f w : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    (hw : ∀ k, StronglyMeasurable[ℱ k] (w (k+1)))
    (hi : ∀ k, ∀ᵐ ω ∂P, |ordinaryDiff f (k+1) ω| ≤ w (k+1) ω)
    (hzero : f 0 = 0) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (t : ℝ) (ht : 0 < t) :
    P {ω | 2*t < squareReal f N ω} ≤ P {ω | δ*t < maxReal f N ω} +
      P {ω | δ*t < maxReal w N ω} + ENNReal.ofReal (32*δ^2) * P {ω | t < squareReal f N ω} := by
  have hm : ∀ k, Measurable (f k) := fun k => ((hf.stronglyAdapted k).mono (ℱ.le k)).measurable
  have hU := maxReal_measurable (fun k => hm (k+1)) N
  have hV := squareReal_measurable hm N
  have hW := maxReal_measurable (fun k => ((hw k).mono (ℱ.le k)).measurable) N
  apply tail_union_bound
  let E := {ω | 2*t < squareReal f N ω ∧ maxReal f N ω ≤ δ*t ∧ maxReal w N ω ≤ δ*t}
  have hE : MeasurableSet E := (measurableSet_lt measurable_const hV).inter
    ((measurableSet_le hU measurable_const).inter (measurableSet_le hW measurable_const))
  have hp := square_segment_probability hf hw hi hzero N ht (by positivity : 0 ≤ δ*t)
    (by nlinarith : δ*t ≤ t) hE (fun ω hω => by
      refine ⟨?_, ?_, ?_⟩
      · rw [pathEnergy_eq_squareReal_sq f hzero]
        have h := hω.1
        nlinarith [squareReal_nonneg f N ω]
      · intro k hk hkn
        exact (abs_le_maxReal f (Finset.mem_Icc.mpr ⟨hk,hkn⟩) ω).trans hω.2.1
      · intro k hk hkn
        exact (le_abs_self _).trans ((abs_le_maxReal w (Finset.mem_Icc.mpr ⟨hk,hkn⟩) ω).trans hω.2.2))
  have heq : {ω | t^2 < pathEnergy (fun j => f j ω) N} = {ω | t < squareReal f N ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, pathEnergy_eq_squareReal_sq f hzero]
    have h := squareReal_nonneg f N ω
    constructor <;> intro hh <;> nlinarith
  rw [heq] at hp
  apply measure_le_of_real (by positivity)
  have hmul : t^2 * P.real E ≤ t^2 * (16*δ^2*P.real {ω | t < squareReal f N ω}) := by nlinarith [hp]
  have hdiv := (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp hmul
  exact hdiv.trans (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg δ]) measureReal_nonneg)

end BurkholderDFI.ConvexPhi.Proof
-- End SquareTail

-- Begin MaxSegment

namespace BurkholderDFI.ConvexPhi.Proof

noncomputable def maxStop (g w : ℕ → ℝ) (b : ℝ) (N : ℕ) : ℕ :=
  min (finiteHit (fun j => b^2 < pathEnergy g j) N) (finiteHit (fun j => b < w (j+1)) N)
noncomputable def maxStart (g w : ℕ → ℝ) (l b : ℝ) (N : ℕ) : ℕ :=
  min (finiteHit (fun j => l < |g j|) N) (maxStop g w b N)
lemma maxStart_le_stop (g w : ℕ → ℝ) (l b : ℝ) (N : ℕ) :
    maxStart g w l b N ≤ maxStop g w b N := min_le_right _ _
lemma maxStop_le_end (g w : ℕ → ℝ) (b : ℝ) (N : ℕ) :
    maxStop g w b N ≤ N := (min_le_left _ _).trans (finiteHit_le _ N)

lemma maxSegment_energy_bound (g w : ℕ → ℝ) (N : ℕ) {l b : ℝ}
    (hb : 0 ≤ b) (hi : ∀ k, 0 < k → k ≤ N → |g k-g (k-1)| ≤ w k) :
    (∑ k ∈ Finset.range N, segmentIncrement (maxStart g w l b N)
      (maxStop g w b N) g (k+1)^2) ≤ 2*b^2 := by
  have h := energy_at_stopped_bound g w N hb hi
    (k := maxStop g w b N) (min_le_left _ _) (min_le_right _ _)
  have hs := segment_energy_le_end (maxStart_le_stop g w l b N) g N
  rw [min_eq_left (maxStop_le_end g w b N)] at hs
  change _ ≤ pathEnergy g (maxStop g w b N) at hs
  linarith

lemma maxSegment_zero_energy (g w : ℕ → ℝ) (N : ℕ) {l b : ℝ}
    (hM : ∀ k ≤ N, |g k| ≤ l) :
    ∑ k ∈ Finset.range N, segmentIncrement (maxStart g w l b N)
      (maxStop g w b N) g (k+1)^2 = 0 := by
  have hm : finiteHit (fun j => l < |g j|) N = N :=
    finiteHit_eq_end (fun k hk => not_lt_of_ge (hM k hk.le))
  have hs : maxStart g w l b N = maxStop g w b N := by
    rw [maxStart, hm, min_eq_right (maxStop_le_end g w b N)]
  simp only [hs, segment_zero_of_reverse le_rfl, zero_pow (by omega : (2:ℕ) ≠ 0), Finset.sum_const_zero]

lemma maxSegment_target (g w : ℕ → ℝ) (N : ℕ) {l b : ℝ}
    (hl : 0 < l) (hb : 0 ≤ b) (hbl : b ≤ l/2) (hg0 : g 0 = 0)
    (hi : ∀ k, 0 < k → k ≤ N → |g k-g (k-1)| ≤ w k)
    (hS : pathEnergy g N ≤ b^2)
    (hw : ∀ k, 0 < k → k ≤ N → w k ≤ b)
    (hM : ∃ k ≤ N, 2*l < |g k|) :
    ∃ r ≤ N, l/2 < |∑ k ∈ Finset.range r, segmentIncrement (maxStart g w l b N)
      (maxStop g w b N) g (k+1)| := by
  have htS : finiteHit (fun j => b^2 < pathEnergy g j) N = N :=
    finiteHit_eq_end (fun k hk => not_lt_of_ge ((pathEnergy_mono g hk.le).trans hS))
  have htw : finiteHit (fun j => b < w (j+1)) N = N :=
    finiteHit_eq_end (fun k hk => not_lt_of_ge (hw (k+1) (by omega) (by omega)))
  have ht : maxStop g w b N = N := by simp [maxStop, htS, htw]
  have ha : maxStart g w l b N = finiteHit (fun j => l < |g j|) N := by
    rw [maxStart, ht, min_eq_left (finiteHit_le _ N)]
  obtain ⟨r,hr,hval⟩ := hM
  have hμr : finiteHit (fun j => l < |g j|) N ≤ r := finiteHit_le_of (by linarith : l < |g r|)
  have hv := value_at_stopped_bound g w N hl.le hb hg0 hi
    (k := finiteHit (fun j => l < |g j|) N) le_rfl (by rw [htw]; exact finiteHit_le _ N)
  refine ⟨r, hr, ?_⟩
  rw [segment_sum (maxStart_le_stop g w l b N), ht, min_eq_right hr, ha, min_eq_left hμr]
  have htri := abs_add_le (g r-g (finiteHit (fun j => l < |g j|) N))
    (g (finiteHit (fun j => l < |g j|) N))
  rw [sub_add_cancel] at htri
  linarith

end BurkholderDFI.ConvexPhi.Proof
-- End MaxSegment

-- Begin FiniteMaximalEnergy

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

lemma finite_maximal_energy {e : ℕ → Ω → ℝ} (ha : StronglyAdapted ℱ e)
    (h2 : ∀ k, MemLp (e k) 2 P) (hz : ∀ k, P[e (k+1)|ℱ k] =ᵐ[P] 0)
    (N : ℕ) {r : ℝ} (hr : 0 < r) {E : Set Ω} (hE : MeasurableSet E)
    (ht : ∀ᵐ ω ∂P, ω ∈ E → ∃ k ≤ N, r < |partialProcess e k ω|) :
    r^2 * P.real E ≤ ∑ k ∈ Finset.range N, ∫ ω, e (k+1) ω^2 ∂P := by
  let τ : Ω → ℕ := fun ω => finiteHit (fun k => r < |partialProcess e k ω|) N
  let A : ℕ → Set Ω := segmentEvents (fun _ => 0) τ
  let u := maskedIncrement A e
  have hzero : ∀ k, MeasurableSet[ℱ k] {ω : Ω | (0:ℕ) ≤ k} := by
    intro k
    let : MeasurableSpace Ω := ℱ k
    simp
  have hτ := valueHit_measurable (partialProcess_adapted ha) r N
  have hAm : ∀ k, MeasurableSet (A k) := fun k => ℱ.le k _ (segmentEvents_adapted hzero hτ k)
  have hu2 : ∀ k, MemLp (u k) 2 P := maskedIncrement_memLp hAm h2
  have hum : StronglyAdapted ℱ u := maskedIncrement_adapted (segmentEvents_adapted hzero hτ) ha
  have huz : ∀ k, P[u (k+1)|ℱ k] =ᵐ[P] 0 :=
    maskedIncrement_condExp_zero (segmentEvents_predictable hzero hτ)
      (fun k => (h2 k).integrable (by norm_num)) hz
  have hid : ∀ ω, partialProcess u N ω = partialProcess e (τ ω) ω := by
    intro ω
    simp only [partialProcess, Finset.sum_apply, u, maskedIncrement]
    have h := sum_mask_interval (Nat.zero_le (τ ω)) (fun k => e k ω) N
    have hτN : τ ω ≤ N := finiteHit_le _ N
    simp only [Nat.zero_lt_succ, true_and, min_eq_left hτN,
      Nat.zero_min, Finset.sum_range_zero, sub_zero] at h
    simpa only [A, segmentEvents, Set.indicator_apply, Set.mem_ofPred_eq,
      Nat.zero_lt_succ, true_and, partialProcess, Finset.sum_apply] using h
  have hlow : ∀ᵐ ω ∂P, E.indicator (fun _ => r^2) ω ≤ partialProcess u N ω^2 := by
    filter_upwards [ht] with ω hω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he, hid]
      obtain ⟨k,hk,hval⟩ := hω he
      have hτk : τ ω ≤ k := finiteHit_le_of hval
      have hh : r < |partialProcess e (τ ω) ω| := by
        rcases finiteHit_spec (fun k => r < |partialProcess e k ω|) N with h | h
        · exact h
        · have heq : τ ω = k := by change τ ω = N at h; omega
          simpa only [heq] using hval
      nlinarith [sq_abs (partialProcess e (τ ω) ω)]
    · rw [Set.indicator_of_notMem he]
      exact sq_nonneg _
  calc
    _ ≤ ∫ ω, partialProcess u N ω^2 ∂P := event_le_integral_sq (partialProcess_memLp hu2 N) hE hlow
    _ = ∑ k ∈ Finset.range N, ∫ ω, u (k+1) ω^2 ∂P := partialProcess_energy hum hu2 huz N
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      apply integral_mono (hu2 (k+1)).integrable_sq (h2 (k+1)).integrable_sq
      intro ω
      change ((A (k+1)).indicator (e (k+1)) ω)^2 ≤ _
      by_cases h : ω ∈ A (k+1)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, zero_pow (by omega : (2:ℕ) ≠ 0)]
        exact sq_nonneg _

end BurkholderDFI.ConvexPhi.Proof
-- End FiniteMaximalEnergy

-- Begin EventEnergyUpper

open MeasureTheory ProbabilityTheory
namespace BurkholderDFI.ConvexPhi.Proof
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
lemma integral_energy_le_event {e : ℕ → Ω → ℝ} (he : ∀ k, MemLp (e k) 2 P)
    (n : ℕ) {A : Set Ω} (hA : MeasurableSet A) {b : ℝ}
    (hbound : ∀ᵐ ω ∂P, (∑ k ∈ Finset.range n, e (k+1) ω ^ 2) ≤
      A.indicator (fun _ => b) ω) :
    (∑ k ∈ Finset.range n, ∫ ω, e (k+1) ω ^ 2 ∂P) ≤ b * P.real A := by
  have hi : Integrable (A.indicator (fun _ : Ω => b)) P := integrable_const _ |>.indicator hA
  have hs : Integrable (fun ω => ∑ k ∈ Finset.range n, e (k+1) ω ^ 2) P :=
    integrable_finsetSum _ (fun k _ => (he (k+1)).integrable_sq)
  calc
    _ = ∫ ω, ∑ k ∈ Finset.range n, e (k+1) ω ^ 2 ∂P :=
      (integral_finsetSum _ (fun k _ => (he (k+1)).integrable_sq)).symm
    _ ≤ ∫ ω, A.indicator (fun _ => b) ω ∂P := integral_mono_ae hs hi hbound
    _ = _ := by rw [integral_indicator hA, setIntegral_const]; simp [mul_comm]
end BurkholderDFI.ConvexPhi.Proof
-- End EventEnergyUpper

-- Begin MaxProbability

open MeasureTheory ProbabilityTheory

namespace BurkholderDFI.ConvexPhi.Proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

lemma max_segment_probability {f w : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    (hw : ∀ k, StronglyMeasurable[ℱ k] (w (k+1)))
    (hi : ∀ k, ∀ᵐ ω ∂P, |ordinaryDiff f (k+1) ω| ≤ w (k+1) ω)
    (hzero : f 0 = 0) (N : ℕ) {l b : ℝ} (hl : 0 < l) (hb : 0 ≤ b) (hbl : b ≤ l/2)
    {E : Set Ω} (hE : MeasurableSet E)
    (htarget : ∀ ω ∈ E, pathEnergy (fun j => f j ω) N ≤ b^2 ∧
      (∀ k, 0 < k → k ≤ N → w k ω ≤ b) ∧ (∃ k ≤ N, 2*l < |f k ω|)) :
    (l/2)^2 * P.real E ≤ (2*b^2) * P.real {ω | ∃ k ≤ N, l < |f k ω|} := by
  let a : Ω → ℕ := fun ω => maxStart (fun j => f j ω) (fun j => w j ω) l b N
  let z : Ω → ℕ := fun ω => maxStop (fun j => f j ω) (fun j => w j ω) b N
  let e := stochasticSegment f a z
  have hzM : ∀ k, MeasurableSet[ℱ k] {ω | z ω ≤ k} :=
    stopping_min_measurable (energyHit_measurable hf.stronglyAdapted b N) (jumpHit_measurable hw b N)
  have haM : ∀ k, MeasurableSet[ℱ k] {ω | a ω ≤ k} :=
    stopping_min_measurable (valueHit_measurable hf.stronglyAdapted l N) hzM
  have h2 : ∀ k, MemLp (e k) 2 P := stochasticSegment_memLp hf haM hzM hb N
    (fun _ => min_le_right _ _) hi
  have had : StronglyAdapted ℱ e := maskedIncrement_adapted (segmentEvents_adapted haM hzM)
    (ordinaryDiff_adapted hf.stronglyAdapted)
  have hmean := stochasticSegment_condExp_zero hf haM hzM
  have hA : MeasurableSet {ω | ∃ k ≤ N, l < |f k ω|} := by
    have he : {ω | ∃ k ≤ N, l < |f k ω|} = ⋃ k : ℕ, ⋃ (_ : k ≤ N), {ω | l < |f k ω|} := by
      ext ω; simp
    rw [he]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const ((hf.stronglyAdapted k).mono (ℱ.le k)).measurable.abs
  have hp : ∀ᵐ ω ∂P, ∀ k, 0 < k → k ≤ N → |f k ω-f (k-1) ω| ≤ w k ω := by
    filter_upwards [ae_all_iff.mpr hi] with ω hω
    intro k hk _
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact hω j
  have hlow : ∀ᵐ ω ∂P, ω ∈ E → ∃ k ≤ N, l/2 < |partialProcess e k ω| := by
    filter_upwards [hp] with ω hω
    intro he
    have ht := htarget ω he
    have h := maxSegment_target (fun j => f j ω) (fun j => w j ω) N hl hb hbl
      (congrFun hzero ω) hω ht.1 ht.2.1 ht.2.2
    simpa only [partialProcess, Finset.sum_apply, e, stochasticSegment_apply, a, z] using h
  have hupp : ∀ᵐ ω ∂P, (∑ k ∈ Finset.range N, e (k+1) ω^2) ≤
      {ω | ∃ k ≤ N, l < |f k ω|}.indicator (fun _ => 2*b^2) ω := by
    filter_upwards [hp] with ω hω
    simp only [e, stochasticSegment_apply, a, z]
    by_cases he : ∃ k ≤ N, l < |f k ω|
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, he, if_true]
      exact maxSegment_energy_bound _ _ N hb hω
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, he, if_false]
      have hm : ∀ k ≤ N, |f k ω| ≤ l := by
        intro k hk
        exact le_of_not_gt (fun h => he ⟨k,hk,h⟩)
      rw [maxSegment_zero_energy _ _ N hm]
  exact (finite_maximal_energy had h2 hmean N (by linarith) hE hlow).trans
    (integral_energy_le_event h2 N hA hupp)

end BurkholderDFI.ConvexPhi.Proof
-- End MaxProbability

-- Begin MaxTail

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BurkholderDFI.ConvexPhi.Proof
variable {Ω : Type*}

lemma maxReal_gt_iff (f : ℕ → Ω → ℝ) (hzero : f 0 = 0) (N : ℕ) (ω : Ω)
    {t : ℝ} (ht : 0 < t) : (∃ k ≤ N, t < |f k ω|) ↔ t < maxReal f N ω := by
  constructor
  · rintro ⟨k,hk,hval⟩
    have hk0 : 0 < k := by
      by_contra hh
      have he : k=0 := by omega
      simp only [he,hzero,Pi.zero_apply,abs_zero] at hval
      linarith
    exact hval.trans_le (abs_le_maxReal f (Finset.mem_Icc.mpr ⟨hk0,hk⟩) ω)
  · intro h
    by_contra hh
    have hb : maxReal f N ω ≤ t := maxReal_le f N ω ht.le (fun k hk =>
      le_of_not_gt (fun hgt => hh ⟨k,(Finset.mem_Icc.mp hk).2,hgt⟩))
    linarith

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}

lemma max_goodLambda {f w : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    (hw : ∀ k, StronglyMeasurable[ℱ k] (w (k+1)))
    (hi : ∀ k, ∀ᵐ ω ∂P, |ordinaryDiff f (k+1) ω| ≤ w (k+1) ω)
    (hzero : f 0 = 0) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (t : ℝ) (ht : 0 < t) :
    P {ω | 2*t < maxReal f N ω} ≤ P {ω | δ*t < squareReal f N ω} +
      P {ω | δ*t < maxReal w N ω} + ENNReal.ofReal (32*δ^2) * P {ω | t < maxReal f N ω} := by
  have hm : ∀ k, Measurable (f k) := fun k => ((hf.stronglyAdapted k).mono (ℱ.le k)).measurable
  have hV := maxReal_measurable (fun k => hm (k+1)) N
  have hU := squareReal_measurable hm N
  have hW := maxReal_measurable (fun k => ((hw k).mono (ℱ.le k)).measurable) N
  apply tail_union_bound
  let E := {ω | 2*t < maxReal f N ω ∧ squareReal f N ω ≤ δ*t ∧ maxReal w N ω ≤ δ*t}
  have hE : MeasurableSet E := (measurableSet_lt measurable_const hV).inter
    ((measurableSet_le hU measurable_const).inter (measurableSet_le hW measurable_const))
  have hp := max_segment_probability hf hw hi hzero N ht (by positivity : 0 ≤ δ*t)
    (by nlinarith : δ*t ≤ t/2) hE (fun ω hω => by
      refine ⟨?_, ?_, ?_⟩
      · rw [pathEnergy_eq_squareReal_sq f hzero]
        have h := hω.2.1
        nlinarith [squareReal_nonneg f N ω]
      · intro k hk hkn
        exact (le_abs_self _).trans ((abs_le_maxReal w (Finset.mem_Icc.mpr ⟨hk,hkn⟩) ω).trans hω.2.2)
      · exact (maxReal_gt_iff f hzero N ω (by linarith : 0 < 2*t)).mpr hω.1)
  have heq : {ω | ∃ k ≤ N, t < |f k ω|} = {ω | t < maxReal f N ω} := by
    ext ω
    exact maxReal_gt_iff f hzero N ω ht
  rw [heq] at hp
  apply measure_le_of_real (by positivity)
  have hmul : t^2 * P.real E ≤ t^2 * (8*δ^2*P.real {ω | t < maxReal f N ω}) := by nlinarith [hp]
  have hdiv := (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp hmul
  exact hdiv.trans (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg δ]) measureReal_nonneg)

end BurkholderDFI.ConvexPhi.Proof
-- End MaxTail

-- Begin DyadicScalar

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma sum_weights_below (w : ℤ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hstep : ∀ i j, i < j → 2*w i ≤ w j) (s : Finset ℤ) :
    ∀ b, (∀ j ∈ s, j < b) → ∑ j ∈ s, w j ≤ w b := by
  induction s using Finset.induction_on_max with
  | empty => intro b _; simpa using hw b
  | insert i s his ih =>
    intro b hb
    have hi : i ∉ s := fun h => (lt_irrefl i) (his i h)
    rw [Finset.sum_insert hi]
    have hs := ih i his
    have ht := hstep i b (hb i (Finset.mem_insert_self _ _))
    linarith

lemma dyadic_weight_step (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) (i j : ℤ) (hij : i < j) :
    2*phiReal Φ ((2:ℝ)^i) ≤ phiReal Φ ((2:ℝ)^j) := by
  have he : 2*(2:ℝ)^i = (2:ℝ)^(i+1) := by rw [zpow_add₀ (by norm_num)]; ring
  exact (phiReal_lower_double hΦ hcv (by positivity)).trans
    (phiReal_mono hΦ (by rw [he]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)))

lemma dyadic_sum_le (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) (s : Finset ℤ) (x : ℝ) :
    (∑ j ∈ s, if (2:ℝ)^j < x then phiReal Φ ((2:ℝ)^j) else 0) ≤ 2*phiReal Φ x := by
  classical
  let t := s.filter (fun j => (2:ℝ)^j < x)
  have he : (∑ j ∈ s, if (2:ℝ)^j < x then phiReal Φ ((2:ℝ)^j) else 0) =
      ∑ j ∈ t, phiReal Φ ((2:ℝ)^j) := by simp [t, Finset.sum_filter]
  rw [he]
  rcases t.eq_empty_or_nonempty with ht | ht
  · rw [ht, Finset.sum_empty]; exact mul_nonneg (by norm_num) (phiReal_nonneg x)
  let b := t.max' ht
  have hb : b ∈ t := Finset.max'_mem t ht
  have hs := sum_weights_below (fun j => phiReal Φ ((2:ℝ)^j))
    (fun j => phiReal_nonneg _) (dyadic_weight_step hΦ hcv) (t.erase b) b
    (fun j hj => t.lt_max'_of_mem_erase_max' ht hj)
  have hx : phiReal Φ ((2:ℝ)^b) ≤ phiReal Φ x :=
    phiReal_mono hΦ (Finset.mem_filter.mp hb).2.le
  have hsum := Finset.sum_erase_add t (fun j => phiReal Φ ((2:ℝ)^j)) hb
  linarith

noncomputable def dyadicGauge (Φ : ℝ≥0∞ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, if (2:ℝ)^j < x then Φ (ENNReal.ofReal ((2:ℝ)^j)) else 0

lemma dyadicGauge_le (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) (x : ℝ) :
    dyadicGauge Φ x ≤ 2 * Φ (ENNReal.ofReal x) := by
  rw [dyadicGauge, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have he : (∑ j ∈ s, if (2:ℝ)^j < x then Φ (ENNReal.ofReal ((2:ℝ)^j)) else 0) =
      ENNReal.ofReal (∑ j ∈ s, if (2:ℝ)^j < x then phiReal Φ ((2:ℝ)^j) else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs; exact phiReal_nonneg _; exact le_rfl)]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [ofReal_phiReal hΦ]
  rw [he, ← ofReal_phiReal hΦ x, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal (dyadic_sum_le hΦ hcv s x)

lemma phi_le_dyadicGauge (hΦ : IsPhi Φ c) {x : ℝ} (hx : 0 ≤ x) :
    Φ (ENNReal.ofReal x) ≤ c * dyadicGauge Φ x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [hΦ.zero]
  obtain ⟨j, hj, hj'⟩ := exists_mem_Ioc_zpow hx (by norm_num : (1:ℝ)<2)
  have he : (2:ℝ)^(j+1) = 2*(2:ℝ)^j := by rw [zpow_add₀ (by norm_num)]; ring
  calc
    Φ (ENNReal.ofReal x) ≤ Φ (ENNReal.ofReal ((2:ℝ)^(j+1))) := hΦ.mono (ENNReal.ofReal_le_ofReal hj')
    _ = Φ (2*ENNReal.ofReal ((2:ℝ)^j)) := by rw [he, ENNReal.ofReal_mul (by norm_num)]; norm_num
    _ ≤ c * Φ (ENNReal.ofReal ((2:ℝ)^j)) := hΦ.growth _
    _ ≤ c * dyadicGauge Φ x := mul_le_mul' le_rfl (by
      exact (by simpa only [if_pos hj, dyadicGauge] using (ENNReal.le_tsum (f := fun i : ℤ => if (2:ℝ)^i < x then Φ (ENNReal.ofReal ((2:ℝ)^i)) else 0) j)))

end BurkholderDFI.ConvexPhi.Proof
-- End DyadicScalar

-- Begin DyadicIntegral

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

noncomputable def dyadicTail (P : Measure Ω) (Φ : ℝ≥0∞ → ℝ≥0∞) (X : Ω → ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, Φ (ENNReal.ofReal ((2:ℝ)^j)) * P {ω | (2:ℝ)^j < X ω}

lemma lintegral_dyadicGauge (Φ : ℝ≥0∞ → ℝ≥0∞) {X : Ω → ℝ} (hX : Measurable X) :
    (∫⁻ ω, dyadicGauge Φ (X ω) ∂P) = dyadicTail P Φ X := by
  unfold dyadicGauge dyadicTail
  rw [lintegral_tsum]
  · apply tsum_congr
    intro j
    have hs : MeasurableSet {ω | (2:ℝ)^j < X ω} := measurableSet_lt measurable_const hX
    have he : (fun ω => if (2:ℝ)^j < X ω then Φ (ENNReal.ofReal ((2:ℝ)^j)) else 0) =
        Set.indicator {ω | (2:ℝ)^j < X ω} (fun _ => Φ (ENNReal.ofReal ((2:ℝ)^j))) := rfl
    rw [he, lintegral_indicator hs, lintegral_const]
    simp
  · intro j
    exact (measurable_const.indicator (measurableSet_lt measurable_const hX)).aemeasurable

lemma dyadicTail_le (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ) {X : Ω → ℝ} (hX : Measurable X) :
    dyadicTail P Φ X ≤ 2 * ∫⁻ ω, Φ (ENNReal.ofReal (X ω)) ∂P := by
  rw [← lintegral_dyadicGauge Φ hX, ← lintegral_const_mul _ (show Measurable (fun ω => Φ (ENNReal.ofReal (X ω))) from hΦ.cont.measurable.comp hX.ennreal_ofReal)]
  exact lintegral_mono fun ω => dyadicGauge_le hΦ hcv (X ω)

lemma lintegral_phi_le_dyadicTail (hΦ : IsPhi Φ c) {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) :
    (∫⁻ ω, Φ (ENNReal.ofReal (X ω)) ∂P) ≤ c * dyadicTail P Φ X := by
  rw [← lintegral_dyadicGauge Φ hX, ← lintegral_const_mul']
  · exact lintegral_mono fun ω => phi_le_dyadicGauge hΦ (hX0 ω)
  · exact ENNReal.coe_ne_top

lemma dyadicTail_mono {X Y : Ω → ℝ} (hXY : ∀ ω, X ω ≤ Y ω) :
    dyadicTail P Φ X ≤ dyadicTail P Φ Y := by
  apply ENNReal.tsum_le_tsum
  intro j
  exact mul_le_mul' le_rfl (measure_mono fun ω hω => lt_of_lt_of_le hω (hXY ω))

end BurkholderDFI.ConvexPhi.Proof
-- End DyadicIntegral

-- Begin DyadicShift

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma dyadic_weight_add (hΦ : IsPhi Φ c) (j : ℤ) (k : ℕ) :
    Φ (ENNReal.ofReal ((2:ℝ)^(j+(k:ℤ)))) ≤ (c:ℝ≥0∞)^k * Φ (ENNReal.ofReal ((2:ℝ)^j)) := by
  have he : ENNReal.ofReal ((2:ℝ)^(j+(k:ℤ))) = (2:ℝ≥0∞)^k * ENNReal.ofReal ((2:ℝ)^j) := by
    rw [zpow_add₀ (by norm_num), zpow_natCast, mul_comm, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [he]
  exact phi_growth_pow hΦ k _

lemma dyadicTail_shift_lower (hΦ : IsPhi Φ c) (X : Ω → ℝ) :
    dyadicTail P Φ X ≤ c * ∑' j : ℤ, Φ (ENNReal.ofReal ((2:ℝ)^j)) * P {ω | 2*(2:ℝ)^j < X ω} := by
  unfold dyadicTail
  rw [← (Equiv.addRight (1:ℤ)).tsum_eq, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  have he : (2:ℝ)^(j+1) = 2*(2:ℝ)^j := by rw [zpow_add₀ (by norm_num)]; ring
  change Φ (ENNReal.ofReal ((2:ℝ)^(j+1))) * P {ω | (2:ℝ)^(j+1)<X ω} ≤ _
  have hw := dyadic_weight_add hΦ j 1
  simp only [Nat.cast_one, pow_one] at hw
  rw [he]
  rw [he] at hw
  exact (mul_le_mul' hw le_rfl).trans_eq (by ring)

lemma dyadicTail_shift_upper (hΦ : IsPhi Φ c) (X : Ω → ℝ) (k : ℕ) :
    (∑' j : ℤ, Φ (ENNReal.ofReal ((2:ℝ)^j)) *
      P {ω | (2:ℝ)^(-(k:ℤ)) * (2:ℝ)^j < X ω}) ≤ (c:ℝ≥0∞)^k * dyadicTail P Φ X := by
  rw [← (Equiv.addRight (k:ℤ)).tsum_eq]
  unfold dyadicTail
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  have he : (2:ℝ)^(-(k:ℤ)) * (2:ℝ)^(j+(k:ℤ)) = (2:ℝ)^j := by
    rw [← zpow_add₀ (by norm_num)]
    congr 1; omega
  change Φ (ENNReal.ofReal ((2:ℝ)^(j+(k:ℤ)))) *
    P {ω | (2:ℝ)^(-(k:ℤ))*(2:ℝ)^(j+(k:ℤ)) < X ω} ≤ _
  rw [he]
  exact (mul_le_mul' (dyadic_weight_add hΦ j k) le_rfl).trans_eq (by ring)

lemma dyadic_goodLambda (hΦ : IsPhi Φ c) (U V W : Ω → ℝ) (k : ℕ) (q : ℝ≥0∞)
    (hgood : ∀ t : ℝ, 0 < t → P {ω | 2*t < V ω} ≤
      P {ω | (2:ℝ)^(-(k:ℤ))*t < U ω} + P {ω | (2:ℝ)^(-(k:ℤ))*t < W ω} + q*P {ω | t<V ω}) :
    dyadicTail P Φ V ≤ (c:ℝ≥0∞)^(k+1)*(dyadicTail P Φ U+dyadicTail P Φ W) +
      (c:ℝ≥0∞)*q*dyadicTail P Φ V := by
  have hsum := ENNReal.tsum_le_tsum (fun j : ℤ =>
    mul_le_mul' (le_rfl : Φ (ENNReal.ofReal ((2:ℝ)^j)) ≤ _) (hgood ((2:ℝ)^j) (by positivity)))
  simp_rw [mul_add, ENNReal.tsum_add] at hsum
  have he : (∑' j : ℤ, Φ (ENNReal.ofReal ((2:ℝ)^j)) * (q * P {ω | (2:ℝ)^j<V ω})) =
      q*dyadicTail P Φ V := by
    simp only [dyadicTail, ← ENNReal.tsum_mul_left]
    apply tsum_congr; intro j; ring
  rw [he] at hsum
  have hU := dyadicTail_shift_upper (P := P) hΦ U k
  have hW := dyadicTail_shift_upper (P := P) hΦ W k
  calc
    _ ≤ _ := dyadicTail_shift_lower hΦ V
    _ ≤ c * (((c:ℝ≥0∞)^k*dyadicTail P Φ U + (c:ℝ≥0∞)^k*dyadicTail P Φ W) + q*dyadicTail P Φ V) :=
      mul_le_mul' le_rfl (hsum.trans (add_le_add (add_le_add hU hW) le_rfl))
    _ = _ := by ring

end BurkholderDFI.ConvexPhi.Proof
-- End DyadicShift

-- Begin GoodLambdaFinite

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma ennreal_absorb_add {A B r : ℝ≥0∞} (hA : A ≠ ⊤) (hr : r ≤ 1/2)
    (h : A ≤ B+r*A) : A ≤ 2*B := by
  by_cases hB : B = ⊤
  · simp [hB]
  have hh : A ≤ r*A+1*B := by simpa only [one_mul, add_comm] using h
  simpa only [mul_one] using ennreal_absorb_half hA hB hr (by simp : (1:ℝ≥0∞) ≠ ⊤) hh

lemma goodLambda_finite (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    (U V W : Ω → ℝ) (hU : Measurable U) (hV : Measurable V) (hW : Measurable W)
    (hV0 : ∀ ω, 0 ≤ V ω) (hVfin : (∫⁻ ω, Φ (ENNReal.ofReal (V ω)) ∂P) ≠ ⊤)
    (k : ℕ) (q : ℝ≥0∞) (hq : (c:ℝ≥0∞)*q ≤ 1/2)
    (hgood : ∀ t : ℝ, 0 < t → P {ω | 2*t < V ω} ≤
      P {ω | (2:ℝ)^(-(k:ℤ))*t < U ω} + P {ω | (2:ℝ)^(-(k:ℤ))*t < W ω} + q*P {ω | t<V ω}) :
    (∫⁻ ω, Φ (ENNReal.ofReal (V ω)) ∂P) ≤
      4*(c:ℝ≥0∞)^(k+2)*((∫⁻ ω, Φ (ENNReal.ofReal (U ω)) ∂P) +
        ∫⁻ ω, Φ (ENNReal.ofReal (W ω)) ∂P) := by
  have hD : dyadicTail P Φ V ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) hVfin) (dyadicTail_le hΦ hcv hV)
  have hb := ennreal_absorb_add hD hq (dyadic_goodLambda hΦ U V W k q hgood)
  calc
    _ ≤ c*dyadicTail P Φ V := lintegral_phi_le_dyadicTail hΦ hV hV0
    _ ≤ c*(2*((c:ℝ≥0∞)^(k+1)*(dyadicTail P Φ U+dyadicTail P Φ W))) := mul_le_mul' le_rfl hb
    _ ≤ c*(2*((c:ℝ≥0∞)^(k+1)*(2*(∫⁻ ω, Φ (ENNReal.ofReal (U ω)) ∂P)+
        2*(∫⁻ ω, Φ (ENNReal.ofReal (W ω)) ∂P)))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
        (add_le_add (dyadicTail_le hΦ hcv hU) (dyadicTail_le hΦ hcv hW))))
    _ = _ := by ring

end BurkholderDFI.ConvexPhi.Proof
-- End GoodLambdaFinite

-- Begin GoodLambdaLimit

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

omit [IsProbabilityMeasure P] in
lemma goodLambda_clip (U V W : Ω → ℝ) (δ : ℝ) (q : ℝ≥0∞)
    (hgood : ∀ t : ℝ, 0 < t → P {ω | 2*t < V ω} ≤
      P {ω | δ*t < U ω} + P {ω | δ*t < W ω} + q*P {ω | t<V ω}) (R : ℝ) :
    ∀ t : ℝ, 0 < t → P {ω | 2*t < min (V ω) R} ≤
      P {ω | δ*t < U ω} + P {ω | δ*t < W ω} + q*P {ω | t < min (V ω) R} := by
  intro t ht
  by_cases hR : 2*t < R
  · have htR : t < R := by linarith
    simpa only [lt_min_iff, hR, htR, and_true] using hgood t ht
  · simp only [lt_min_iff, hR, and_false, Set.ofPred_false, measure_empty, zero_le]

lemma goodLambda_orlicz (hΦ : IsPhi Φ c) (hcv : IsConvexPhi Φ)
    (U V W : Ω → ℝ) (hU : Measurable U) (hV : Measurable V) (hW : Measurable W)
    (hV0 : ∀ ω, 0 ≤ V ω) (k : ℕ) (q : ℝ≥0∞) (hq : (c:ℝ≥0∞)*q ≤ 1/2)
    (hgood : ∀ t : ℝ, 0 < t → P {ω | 2*t < V ω} ≤
      P {ω | (2:ℝ)^(-(k:ℤ))*t < U ω} + P {ω | (2:ℝ)^(-(k:ℤ))*t < W ω} + q*P {ω | t<V ω}) :
    (∫⁻ ω, Φ (ENNReal.ofReal (V ω)) ∂P) ≤
      4*(c:ℝ≥0∞)^(k+2)*((∫⁻ ω, Φ (ENNReal.ofReal (U ω)) ∂P) +
        ∫⁻ ω, Φ (ENNReal.ofReal (W ω)) ∂P) := by
  have hclip (n : ℕ) := goodLambda_clip U V W ((2:ℝ)^(-(k:ℤ))) q hgood (n:ℝ)
  have hm (n : ℕ) : Measurable (fun ω => Φ (ENNReal.ofReal (min (V ω) (n:ℝ)))) :=
    hΦ.cont.measurable.comp ((hV.min measurable_const).ennreal_ofReal)
  have hmono : Monotone (fun n : ℕ => fun ω => Φ (ENNReal.ofReal (min (V ω) (n:ℝ)))) := by
    intro i j hij ω
    exact hΦ.mono (ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hij)))
  have he (ω : Ω) : Φ (ENNReal.ofReal (V ω)) = ⨆ n : ℕ, Φ (ENNReal.ofReal (min (V ω) (n:ℝ))) := by
    apply le_antisymm
    · obtain ⟨n, hn⟩ := exists_nat_ge (V ω)
      exact le_iSup_of_le n (by rw [min_eq_left hn])
    · exact iSup_le fun n => hΦ.mono (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  simp_rw [he]
  rw [lintegral_iSup hm hmono]
  apply iSup_le
  intro n
  have hfin : (∫⁻ ω, Φ (ENNReal.ofReal (min (V ω) (n:ℝ))) ∂P) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (phi_ofReal_ne_top hΦ (n:ℝ))
    calc
      _ ≤ ∫⁻ _ : Ω, Φ (ENNReal.ofReal (n:ℝ)) ∂P :=
        lintegral_mono fun ω => hΦ.mono (ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = _ := by simp
  exact goodLambda_finite hΦ hcv U (fun ω => min (V ω) (n:ℝ)) W hU
    (hV.min measurable_const) hW (fun ω => le_min (hV0 ω) (Nat.cast_nonneg n)) hfin k q hq (hclip n)

end BurkholderDFI.ConvexPhi.Proof
-- End GoodLambdaLimit

-- Begin GoodLambdaUniform

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp

lemma isPhi_mono_constant {Φ : ℝ≥0∞ → ℝ≥0∞} {c d : ℝ≥0} (hΦ : IsPhi Φ c) (hcd : c ≤ d) :
    IsPhi Φ d :=
  ⟨hΦ.mono, hΦ.cont, hΦ.zero, fun x => (hΦ.growth x).trans (mul_le_mul' (by exact_mod_cast hcd) le_rfl)⟩

lemma exists_goodLambda_scale (a : ℝ≥0) : ∃ k : ℕ, 1 ≤ k ∧
    (a:ℝ)* (32*((2:ℝ)^(-(k:ℤ)))^2) ≤ 1/2 := by
  have ht : Tendsto (fun k : ℕ => (a:ℝ)*(32*((1/2:ℝ)^k)^2)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
    simpa using (h.pow 2 |>.const_mul 32 |>.const_mul (a:ℝ))
  obtain ⟨k, hk₁, hk₂⟩ := ((eventually_ge_atTop 1).and
    (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))).exists
  refine ⟨k, hk₁, ?_⟩
  simpa [zpow_neg, one_div, inv_pow] using hk₂.le

lemma goodLambda_uniform (c : ℝ≥0) : ∃ (δ : ℝ) (K : ℝ≥0),
    0 < δ ∧ δ ≤ 1/2 ∧ 0 < K ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Φ : ℝ≥0∞ → ℝ≥0∞), IsPhi Φ c → IsConvexPhi Φ →
    ∀ (U V W : Ω → ℝ), Measurable U → Measurable V → Measurable W → (∀ ω, 0 ≤ V ω) →
    (∀ t : ℝ, 0 < t → P {ω | 2*t<V ω} ≤ P {ω | δ*t<U ω}+P {ω | δ*t<W ω}+
      ENNReal.ofReal (32*δ^2)*P {ω | t<V ω}) →
    (∫⁻ ω, Φ (ENNReal.ofReal (V ω)) ∂P) ≤
      K*((∫⁻ ω, Φ (ENNReal.ofReal (U ω)) ∂P)+(∫⁻ ω, Φ (ENNReal.ofReal (W ω)) ∂P)) := by
  let a : ℝ≥0 := c+2
  obtain ⟨k, hk, hsmall⟩ := exists_goodLambda_scale a
  refine ⟨(2:ℝ)^(-(k:ℤ)), 1+4*a^(k+2), by positivity, ?_, by positivity, ?_⟩
  · have h : -(k:ℤ) ≤ -1 := by omega
    have hh := zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) h
    simpa using hh
  · intro Ω mΩ P hP Φ hΦ hcv U V W hU hV hW hV0 hgood
    have hΦa := isPhi_mono_constant hΦ (show c ≤ a from le_add_of_nonneg_right (by positivity))
    have hq : (a:ℝ≥0∞)*ENNReal.ofReal (32*((2:ℝ)^(-(k:ℤ)))^2) ≤ 1/2 := by
      have h := ENNReal.ofReal_le_ofReal hsmall
      rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_div_of_pos (by norm_num)] at h
      simpa using h
    have h := goodLambda_orlicz hΦa hcv U V W hU hV hW hV0 k _ hq hgood
    refine h.trans (mul_le_mul' ?_ le_rfl)
    push_cast
    exact le_add_of_nonneg_left (by positivity)

end BurkholderDFI.ConvexPhi.Proof
-- End GoodLambdaUniform

-- Begin PredictableOrlicz

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.ConvexPhi.Proof

lemma predictable_orlicz_uniform (c : ℝ≥0) : ∃ K : ℝ≥0, 0 < K ∧
    ∀ (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ mΩ) (f w : ℕ → Ω → ℝ), Martingale f ℱ P →
      (∀ k, StronglyMeasurable[ℱ k] (w (k+1))) →
      (∀ k, ∀ᵐ ω ∂P, |ordinaryDiff f (k+1) ω| ≤ w (k+1) ω) → f 0 = 0 →
      ∀ Φ : ℝ≥0∞ → ℝ≥0∞, IsPhi Φ c → IsConvexPhi Φ → ∀ N : ℕ,
      phiMoment P Φ (squareReal f N) ≤ K*(phiMoment P Φ (maxReal f N)+phiMoment P Φ (maxReal w N)) ∧
      phiMoment P Φ (maxReal f N) ≤ K*(phiMoment P Φ (squareReal f N)+phiMoment P Φ (maxReal w N)) := by
  obtain ⟨δ,K,hδ,hδh,hK,hbound⟩ := goodLambda_uniform c
  refine ⟨K,hK,?_⟩
  intro Ω mΩ P hP ℱ f w hf hw hi hzero Φ hΦ hcv N
  have hm : ∀ k, Measurable (f k) := fun k => ((hf.stronglyAdapted k).mono (ℱ.le k)).measurable
  have hM := maxReal_measurable (fun k => hm (k+1)) N
  have hS := squareReal_measurable hm N
  have hW := maxReal_measurable (fun k => ((hw k).mono (ℱ.le k)).measurable) N
  constructor
  · exact hbound Ω P Φ hΦ hcv (maxReal f N) (squareReal f N) (maxReal w N) hM hS hW
      (squareReal_nonneg f N) (square_goodLambda hf hw hi hzero N hδ hδh)
  · exact hbound Ω P Φ hΦ hcv (squareReal f N) (maxReal f N) (maxReal w N) hS hM hW
      (maxReal_nonneg f N) (max_goodLambda hf hw hi hzero N hδ hδh)

end BurkholderDFI.ConvexPhi.Proof
-- End PredictableOrlicz

-- Begin DavisPredictableOrlicz

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.ConvexPhi.Proof

lemma davis_predictable_orlicz (c : ℝ≥0) : ∃ K : ℝ≥0, 0 < K ∧
    ∀ (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
      ∀ Φ : ℝ≥0∞ → ℝ≥0∞, IsPhi Φ c → IsConvexPhi Φ → ∀ N : ℕ,
      phiMoment P Φ (squareReal (davisGood ℱ P f) N) ≤
        K*(phiMoment P Φ (maxReal (davisGood ℱ P f) N)+phiMoment P Φ (fun ω => 4*maxReal (dseq f) N ω)) ∧
      phiMoment P Φ (maxReal (davisGood ℱ P f) N) ≤
        K*(phiMoment P Φ (squareReal (davisGood ℱ P f) N)+phiMoment P Φ (fun ω => 4*maxReal (dseq f) N ω)) := by
  obtain ⟨K,hK,hbound⟩ := predictable_orlicz_uniform c
  refine ⟨K,hK,?_⟩
  intro Ω mΩ P hP ℱ f hf Φ hΦ hcv N
  let w : ℕ → Ω → ℝ := fun k ω => 4*runningAbs (fun j => dseq f j ω) (k-1)
  have hw : ∀ k, StronglyMeasurable[ℱ k] (w (k+1)) := by
    intro k
    simpa only [w, Nat.add_sub_cancel] using
      (runningAbs_adapted (dseq_adapted hf.stronglyAdapted) k).const_mul 4
  have hi : ∀ k, ∀ᵐ ω ∂P, |ordinaryDiff (davisGood ℱ P f) (k+1) ω| ≤ w (k+1) ω := by
    intro k
    rw [ordinaryDiff_eq_dseq _ (davisGood_zero f)]
    simpa only [w, Nat.add_sub_cancel] using davisGood_increment_bound hf k
  have h := hbound Ω P ℱ (davisGood ℱ P f) w (davisGood_martingale hf) hw hi (davisGood_zero f) Φ hΦ hcv N
  have hwle : ∀ ω, maxReal w N ω ≤ 4*maxReal (dseq f) N ω := by
    intro ω
    apply maxReal_le _ _ _ (mul_nonneg (by norm_num) (maxReal_nonneg (dseq f) N ω))
    intro k hk
    have hm := runningAbs_mono (fun j => dseq f j ω) (show k-1 ≤ N by have := (Finset.mem_Icc.mp hk).2; omega)
    rw [runningAbs_eq_maxReal (dseq f) N ω] at hm
    change |4*runningAbs (fun j => dseq f j ω) (k-1)| ≤ _
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (runningAbs_nonneg _ _))]
    exact mul_le_mul_of_nonneg_left hm (by norm_num)
  have hmoment := phiMoment_mono (P := P) hΦ (Filter.Eventually.of_forall hwle)
  exact ⟨h.1.trans (mul_le_mul' le_rfl (add_le_add le_rfl hmoment)),
    h.2.trans (mul_le_mul' le_rfl (add_le_add le_rfl hmoment))⟩

end BurkholderDFI.ConvexPhi.Proof
-- End DavisPredictableOrlicz

-- Begin FiniteUniform

namespace BurkholderDFI.ConvexPhi.Proof
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp

lemma finite_bdg_uniform (c : ℝ≥0) : ∃ C : ℝ≥0, 0 < C ∧
    ∀ (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
    ∀ (Φ : ℝ≥0∞ → ℝ≥0∞), IsPhi Φ c → IsConvexPhi Φ → ∀ n,
      (∫⁻ ω, Φ (sqFnN f n ω) ∂P) ≤ C*(∫⁻ ω, Φ (maxFnN f n ω) ∂P) ∧
      (∫⁻ ω, Φ (maxFnN f n ω) ∂P) ≤ C*(∫⁻ ω, Φ (sqFnN f n ω) ∂P) := by
  obtain ⟨K, _hK, hgood⟩ := davis_predictable_orlicz c
  obtain ⟨L, _hL, hbad⟩ := davis_variation_orlicz_uniform c
  refine ⟨comparisonConstant c K L, comparisonConstant_pos c K L, ?_⟩
  intro Ω mΩ P hP ℱ f hf Φ hΦ hcv n
  have hg := hgood Ω P ℱ f hf Φ hΦ hcv n
  have hh := hbad Ω P ℱ f hf Φ hΦ hcv n
  have h := finite_orlicz_comparison hf hΦ K L n hh hg.1 hg.2
  simpa only [phiMoment, ofReal_squareReal, ofReal_maxReal] using h

end BurkholderDFI.ConvexPhi.Proof
-- End FiniteUniform

-- Begin NativeInfinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BurkholderDFI.SquareFnLp
namespace BurkholderDFI.ConvexPhi.Proof
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
lemma sqFnN_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun n => sqFnN f n ω) := by
  intro n m hnm
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl hnm
  · exact fun _ _ _ => sq_nonneg _

omit [MeasurableSpace Ω] in
lemma maxFnN_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun n => maxFnN f n ω) := by
  intro n m hnm
  apply iSup_le fun k => iSup_le fun hk => ?_
  exact le_iSup_of_le k (le_iSup_of_le ((Finset.Icc_subset_Icc le_rfl hnm) hk) le_rfl)

lemma native_square_moment_iSup {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k))
    {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) :
    (∫⁻ ω, Φ (sqFn f ω) ∂P) = ⨆ n, phiMoment P Φ (squareReal f n) := by
  have he : ∀ ω, Φ (sqFn f ω) = ⨆ n, Φ (sqFnN f n ω) := fun ω =>
    Monotone.map_iSup_of_continuousAt hΦ.cont.continuousAt hΦ.mono hΦ.zero
  simp_rw [he]
  rw [lintegral_iSup]
  · rfl
  · intro n
    exact hΦ.cont.measurable.comp ((squareReal_measurable hf n).ennreal_ofReal)
  · intro n m hnm ω
    exact hΦ.mono (sqFnN_mono f ω hnm)

lemma native_max_moment_iSup {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k))
    {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) :
    (∫⁻ ω, Φ (maxFn f ω) ∂P) = ⨆ n, phiMoment P Φ (maxReal f n) := by
  have he : ∀ ω, Φ (maxFn f ω) = ⨆ n, Φ (maxFnN f n ω) := fun ω =>
    Monotone.map_iSup_of_continuousAt hΦ.cont.continuousAt hΦ.mono hΦ.zero
  have hm : ∀ n, Measurable (fun ω => Φ (maxFnN f n ω)) := by
    intro n
    have h := hΦ.cont.measurable.comp ((maxReal_measurable (fun k => hf (k+1)) n).ennreal_ofReal)
    simpa only [Function.comp_def, ofReal_maxReal] using h
  simp_rw [he]
  rw [lintegral_iSup hm (fun n m hnm ω => hΦ.mono (maxFnN_mono f ω hnm))]
  apply congrArg
  funext n
  simp only [phiMoment, ofReal_maxReal]

lemma finite_bdg_to_infinite {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k))
    {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) (C : ℝ≥0)
    (hfin : ∀ n, phiMoment P Φ (squareReal f n) ≤ C*phiMoment P Φ (maxReal f n) ∧
      phiMoment P Φ (maxReal f n) ≤ C*phiMoment P Φ (squareReal f n)) :
    (∫⁻ ω, Φ (sqFn f ω) ∂P) ≤ C*(∫⁻ ω, Φ (maxFn f ω) ∂P) ∧
    (∫⁻ ω, Φ (maxFn f ω) ∂P) ≤ C*(∫⁻ ω, Φ (sqFn f ω) ∂P) := by
  rw [native_square_moment_iSup hf hΦ, native_max_moment_iSup hf hΦ]
  constructor
  · exact iSup_le fun n => (hfin n).1.trans (mul_le_mul' le_rfl (le_iSup (fun n => phiMoment P Φ (maxReal f n)) n))
  · exact iSup_le fun n => (hfin n).2.trans (mul_le_mul' le_rfl (le_iSup (fun n => phiMoment P Φ (squareReal f n)) n))

end BurkholderDFI.ConvexPhi.Proof
-- End NativeInfinite

-- Begin RootAssembly

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 15.1, p. 33: the two-sided convex Φ inequality. -/
theorem theorem_15_1 (c : ℝ≥0) :
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c → BurkholderDFI.SquareFnLp.IsConvexPhi Φ →
          (C₁ : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P ≤ ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P ∧
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P ≤ (C₂ : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P := by
  obtain ⟨C,hC,hfin⟩ := Proof.finite_bdg_uniform c
  refine ⟨C⁻¹,C,inv_pos.mpr hC,hC,?_⟩
  intro Ω mΩ P hP ℱ f hf Φ hΦ hcv
  have hm : ∀ k, Measurable (f k) := fun k => ((hf.stronglyAdapted k).mono (ℱ.le k)).measurable
  have h := Proof.finite_bdg_to_infinite hm hΦ C (fun n => by
    simpa only [Proof.phiMoment, Proof.ofReal_squareReal, Proof.ofReal_maxReal] using
      hfin Ω P ℱ f hf Φ hΦ hcv n)
  refine ⟨?_,h.2⟩
  have hc : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hh := mul_le_mul' (le_refl ((C : ℝ≥0∞)⁻¹)) h.1
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_mul] at hh
  simpa only [ENNReal.coe_inv hC.ne'] using hh
end BurkholderDFI.ConvexPhi
-- End RootAssembly

-- Begin Solution

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 15.1, p. 33: the two-sided convex Φ inequality. -/
theorem solution (c : ℝ≥0) :
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c → BurkholderDFI.SquareFnLp.IsConvexPhi Φ →
          (C₁ : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P ≤ ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P ∧
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P ≤ (C₂ : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P := by
  exact BurkholderDFI.ConvexPhi.theorem_15_1 c
-- End Solution
