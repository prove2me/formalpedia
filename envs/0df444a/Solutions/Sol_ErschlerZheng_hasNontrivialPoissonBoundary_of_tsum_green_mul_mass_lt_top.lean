-- Prove2me | solution 1 for ErschlerZheng.hasNontrivialPoissonBoundary_of_tsum_green_mul_mass_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T00:07:05.585371+00:00
-- url     : https://prove2.me/submissions/d8f46e44-0532-4ff1-9d43-672762feb2f3

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_isSubgroup_localGermSet_and_germSubgroupoid_closed
import Theorems.Thm_ErschlerZheng_germAction_wellDefined_and_mul
import Theorems.Thm_ErschlerZheng_germConfig_mul_and_injective
import Theorems.Thm_KaimanovichVershik_hasNontrivialPoissonBoundary_iff_exists_isShiftInvariant_pathMeasure_pos_lt_one

section
/-!
# Path space of a random walk (helpers for B7, B8)

Originally for B7: a shift-invariant event of intermediate probability gives a non-trivial Poisson boundary
(Kaimanovich–Vershik, pp. 9–10)

`F(y) = ℙ_y(A)` is `μ`-harmonic by the Markov property at the first step: under the product
measure, a path is its first increment followed by an independent path (`head_tail`), and
shift-invariance turns `W ∈ A` into `(path from y ξ_0) ∈ A`. If `F` were constant `= c` on the
points reachable from `x`, induction on the rank of a cylinder gives
`ℙ(S ∩ W_x⁻¹A) = c ℙ(S)` for every cylinder `S`; the cylinders generate the product σ-algebra,
so `ℙ(W_x⁻¹A) = c²` and `c ∈ {0, 1}`.
-/

open MeasureTheory

namespace ErschlerZheng

namespace B7Dev

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Γ : Type*} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

/-- `(z, ξ) ↦ z ξ_0 ξ_1 ⋯`. -/
def consMap (p : Γ × (ℕ → Γ)) : ℕ → Γ := fun n => match n with
  | 0 => p.1
  | n + 1 => p.2 n

theorem measurable_consMap : Measurable (consMap (Γ := Γ)) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem stepMeasure_apply (μ : Γ → ℝ) (s : Set Γ) :
    stepMeasure μ s = ∑' g, ENNReal.ofReal (μ g) * s.indicator 1 g := by
  unfold stepMeasure
  rw [Measure.sum_apply _ (DiscreteMeasurableSpace.forall_measurableSet s)]
  congr 1; funext g
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _
    (DiscreteMeasurableSpace.forall_measurableSet s)]

theorem isProbabilityMeasure_stepMeasure {μ : Γ → ℝ} (hμ : IsProbability μ) :
    IsProbabilityMeasure (stepMeasure μ) := by
  constructor
  rw [stepMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

theorem lintegral_stepMeasure (μ : Γ → ℝ) (f : Γ → ENNReal) :
    ∫⁻ z, f z ∂stepMeasure μ = ∑' z, ENNReal.ofReal (μ z) * f z := by
  unfold stepMeasure
  rw [lintegral_sum_measure]
  congr 1; funext z
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

/-- The product measure is the first coordinate times an independent copy of itself. -/
theorem head_tail {μ : Γ → ℝ} (hμ : IsProbability μ) :
    haveI := isProbabilityMeasure_stepMeasure hμ
    ((stepMeasure μ).prod (Measure.infinitePi fun _ : ℕ => stepMeasure μ)).map consMap =
      Measure.infinitePi fun _ : ℕ => stepMeasure μ := by
  haveI := isProbabilityMeasure_stepMeasure hμ
  set ν := stepMeasure μ
  set P := Measure.infinitePi fun _ : ℕ => ν
  apply Measure.eq_infinitePi
  intro s t ht
  have hpi : MeasurableSet (Set.pi (↑s) t) := MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply measurable_consMap hpi]
  set T₀ : Set Γ := if 0 ∈ s then t 0 else Set.univ
  set s' : Finset ℕ := s.preimage Nat.succ (Nat.succ_injective.injOn)
  have hset : consMap ⁻¹' Set.pi (↑s) t = T₀ ×ˢ Set.pi (↑s') (fun j => t (j + 1)) := by
    ext ⟨z, ξ⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, s', Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun j hj => h (j + 1) hj⟩
      simp only [T₀]
      split_ifs with h0
      · exact h 0 h0
      · trivial
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simp only [T₀, if_pos hi] at h0; exact h0
      | succ j => exact h1 j hi
  rw [hset, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht (i + 1))]
  -- the product over `s` splits at `0`
  have hsplit : ∏ i ∈ s, ν (t i) =
      (∏ i ∈ s, if i = 0 then ν (t 0) else 1) * ∏ i ∈ s, if i = 0 then 1 else ν (t i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with h
    · subst h; simp
    · simp
  rw [hsplit, Finset.prod_ite_eq' s 0 (fun _ => ν (t 0))]
  congr 1
  · simp only [T₀]; split_ifs <;> simp
  · rw [← Finset.prod_preimage Nat.succ s Nat.succ_injective.injOn
      (fun i => if i = 0 then 1 else ν (t i))]
    · rfl
    · intro x _ hx
      have : x = 0 := by
        by_contra h
        exact hx ⟨x - 1, by simp; omega⟩
      simp [this]

/-- The path from `y`: `W_n = y ξ_0 ⋯ ξ_{n-1}`. -/
def pathMap (y : Γ) (ξ : ℕ → Γ) : ℕ → Γ := fun n => y * (List.ofFn fun i : Fin n => ξ i).prod

theorem measurable_pathMap (y : Γ) : Measurable (pathMap (Γ := Γ) y) := by
  apply measurable_pi_lambda
  intro n
  have h1 : Measurable fun ξ : ℕ → Γ => fun i : Fin n => ξ i :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  exact (measurable_of_countable (fun u : Fin n → Γ => y * (List.ofFn u).prod)).comp h1

theorem pathMap_cons_shift (y z : Γ) (ξ : ℕ → Γ) :
    (fun n => pathMap y (consMap (z, ξ)) (n + 1)) = pathMap (y * z) ξ := by
  funext n
  simp only [pathMap, List.ofFn_succ, List.prod_cons, mul_assoc]
  rfl


/-- `ℙ(E) = Σ_z μ(z) ℙ{ξ : z ξ ∈ E}`. -/
theorem measure_eq_tsum {μ : Γ → ℝ} (hμ : IsProbability μ) {E : Set (ℕ → Γ)} (hE : MeasurableSet E) :
    haveI := isProbabilityMeasure_stepMeasure hμ
    Measure.infinitePi (fun _ : ℕ => stepMeasure μ) E =
      ∑' z, ENNReal.ofReal (μ z) *
        Measure.infinitePi (fun _ : ℕ => stepMeasure μ) {ξ | consMap (z, ξ) ∈ E} := by
  haveI := isProbabilityMeasure_stepMeasure hμ
  conv_lhs => rw [← head_tail hμ]
  rw [Measure.map_apply measurable_consMap hE, Measure.prod_apply (measurable_consMap hE),
    lintegral_stepMeasure]
  rfl

theorem shift_mem {A : Set (ℕ → Γ)} (hAinv : IsShiftInvariant A) (w : ℕ → Γ) :
    w ∈ A ↔ (fun n => w (n + 1)) ∈ A := by
  constructor
  · intro h; rw [← hAinv] at h; exact h
  · intro h; rw [← hAinv]; exact h

theorem cons_mem_path {A : Set (ℕ → Γ)} (hAinv : IsShiftInvariant A) (y z : Γ) (ξ : ℕ → Γ) :
    consMap (z, ξ) ∈ pathMap y ⁻¹' A ↔ ξ ∈ pathMap (y * z) ⁻¹' A := by
  simp only [Set.mem_preimage]
  rw [shift_mem hAinv, pathMap_cons_shift]


end B7Dev

end ErschlerZheng
end

section
/-!
# The orbit chain `P_μ` and its step probabilities in `[0, ∞]` (helpers for B8)

`ofReal (P^{n+1}(y, x)) = Σ_g μ(g) ofReal (P^n(y·g, x))`, so `green` counts the expected visits of
`o·W_n`.
-/

open scoped RightActions ENNReal

namespace ErschlerZheng

namespace B8MarkovDev

open scoped Classical

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X]

theorem orbit_smul' {G : Subgroup H} {o x : X} (hx : x ∈ rightOrbit G o) {g : H} (hg : g ∈ G) :
    x <• g ∈ rightOrbit G o := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k * g, G.mul_mem hk hg, by rw [MulOpposite.op_mul, mul_smul]⟩

/-- `y·g` on the orbit. -/
def oact {G : Subgroup H} {o : X} (y : rightOrbit G o) (g : G) : rightOrbit G o :=
  ⟨(y : X) <• (g : H), orbit_smul' y.2 g.2⟩

theorem orbitKernel_nonneg (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y z : rightOrbit G o) : 0 ≤ orbitKernel G μ o y z :=
  tsum_nonneg fun g => by split_ifs <;> simp [hμ.1 g]

theorem orbitKernel_summand_summable (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y z : rightOrbit G o) :
    Summable fun g : G => if (y : X) <• (g : H) = z then μ g else 0 := by
  refine Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hμ.1 g]) (fun g => ?_)
    hμ.2.summable
  split_ifs
  · exact le_rfl
  · exact hμ.1 g

theorem ofReal_orbitKernel (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y z : rightOrbit G o) :
    ENNReal.ofReal (orbitKernel G μ o y z) =
      ∑' g : G, if oact y g = z then ENNReal.ofReal (μ g) else 0 := by
  unfold orbitKernel
  rw [ENNReal.ofReal_tsum_of_nonneg (fun g => by split_ifs <;> simp [hμ.1 g])
    (orbitKernel_summand_summable G hμ o y z)]
  congr 1; funext g
  by_cases h : (y : X) <• (g : H) = z
  · have h' : oact y g = z := Subtype.ext h
    simp [h, h']
  · have h' : oact y g ≠ z := fun e => h (congrArg Subtype.val e)
    simp [h, h']

theorem tsum_ofReal_orbitKernel (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X)
    (y : rightOrbit G o) : ∑' z, ENNReal.ofReal (orbitKernel G μ o y z) = 1 := by
  simp_rw [ofReal_orbitKernel G hμ o y]
  rw [ENNReal.tsum_comm]
  have : ∀ g : G, (∑' z : rightOrbit G o, if oact y g = z then ENNReal.ofReal (μ g) else 0) =
      ENNReal.ofReal (μ g) := fun g => by
    rw [tsum_eq_single (oact y g) (fun z hz => by rw [if_neg (Ne.symm hz)])]
    simp
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

variable [DecidableEq X]

/-- The step probabilities are in `[0, 1]` and satisfy the first-step recursion over `G`. -/
theorem stepProb_spec (G : Subgroup H) {μ : G → ℝ} (hμ : IsProbability μ) (o : X) :
    ∀ n : ℕ, ∀ y x : rightOrbit G o,
      0 ≤ DurrettProbability.stepProb (orbitKernel G μ o) n y x ∧
        DurrettProbability.stepProb (orbitKernel G μ o) n y x ≤ 1 ∧
        ENNReal.ofReal (DurrettProbability.stepProb (orbitKernel G μ o) (n + 1) y x) =
          ∑' g : G, ENNReal.ofReal (μ g) *
            ENNReal.ofReal (DurrettProbability.stepProb (orbitKernel G μ o) n (oact y g) x) := by
  set P := orbitKernel G μ o
  have hPsum : ∀ y : rightOrbit G o, Summable fun z => P y z := by
    intro y
    have h := ENNReal.summable_toReal (f := fun z => ENNReal.ofReal (P y z))
      (by rw [tsum_ofReal_orbitKernel G hμ o y]; exact ENNReal.one_ne_top)
    exact h.congr fun z => ENNReal.toReal_ofReal (orbitKernel_nonneg G hμ o y z)
  -- the recursion, given bounds at level `n`
  have hrec : ∀ n : ℕ, (∀ z x : rightOrbit G o,
      0 ≤ DurrettProbability.stepProb P n z x ∧ DurrettProbability.stepProb P n z x ≤ 1) →
      ∀ y x : rightOrbit G o, ENNReal.ofReal (DurrettProbability.stepProb P (n + 1) y x) =
        ∑' g : G, ENNReal.ofReal (μ g) *
          ENNReal.ofReal (DurrettProbability.stepProb P n (oact y g) x) := by
    intro n hb y x
    show ENNReal.ofReal (∑' z, P y z * DurrettProbability.stepProb P n z x) = _
    have hsum : Summable fun z => P y z * DurrettProbability.stepProb P n z x := by
      refine Summable.of_nonneg_of_le
        (fun z => mul_nonneg (orbitKernel_nonneg G hμ o y z) (hb z x).1) (fun z => ?_) (hPsum y)
      calc P y z * DurrettProbability.stepProb P n z x ≤ P y z * 1 :=
            mul_le_mul_of_nonneg_left (hb z x).2 (orbitKernel_nonneg G hμ o y z)
        _ = P y z := mul_one _
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun z => mul_nonneg (orbitKernel_nonneg G hμ o y z) (hb z x).1) hsum]
    simp_rw [ENNReal.ofReal_mul (orbitKernel_nonneg G hμ o y _), ofReal_orbitKernel G hμ o y,
      ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1; funext g
    rw [tsum_eq_single (oact y g) (fun z hz => by rw [if_neg (Ne.symm hz), zero_mul])]
    simp
  intro n
  induction n with
  | zero =>
    intro y x
    have hb : ∀ z x : rightOrbit G o, 0 ≤ DurrettProbability.stepProb P 0 z x ∧
        DurrettProbability.stepProb P 0 z x ≤ 1 := by
      intro z x
      simp only [DurrettProbability.stepProb]
      split_ifs <;> norm_num
    exact ⟨(hb y x).1, (hb y x).2, hrec 0 hb y x⟩
  | succ n ih =>
    have hb : ∀ z x : rightOrbit G o, 0 ≤ DurrettProbability.stepProb P (n + 1) z x ∧
        DurrettProbability.stepProb P (n + 1) z x ≤ 1 := by
      intro z x
      refine ⟨tsum_nonneg fun w => mul_nonneg (orbitKernel_nonneg G hμ o z w) (ih w x).1, ?_⟩
      have h1 := (ih z x).2.2
      have h2 : ∑' g : G, ENNReal.ofReal (μ g) *
          ENNReal.ofReal (DurrettProbability.stepProb P n (oact z g) x) ≤ 1 := by
        calc ∑' g : G, ENNReal.ofReal (μ g) *
              ENNReal.ofReal (DurrettProbability.stepProb P n (oact z g) x)
            ≤ ∑' g : G, ENNReal.ofReal (μ g) * 1 := by
              gcongr with g
              exact ENNReal.ofReal_le_one.mpr (ih _ x).2.1
          _ = 1 := by
              simp only [mul_one]
              rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq,
                ENNReal.ofReal_one]
      rw [← h1] at h2
      exact ENNReal.ofReal_le_one.mp h2
    have hb' : ∀ z x : rightOrbit G o, 0 ≤ DurrettProbability.stepProb P n z x ∧
        DurrettProbability.stepProb P n z x ≤ 1 := fun z x => ⟨(ih z x).1, (ih z x).2.1⟩
    intro y x
    exact ⟨(hb y x).1, (hb y x).2, hrec (n + 1) hb y x⟩

end B8MarkovDev

end ErschlerZheng
end

section
/-!
# Germ calculus (helpers for B2, B5, B6)

Composition of germ equalities and multiplicativity of germs come from B1 (imported).
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermBase

set_option linter.unusedSectionVars false

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

theorem rsmul_mul (y : X) (g h : H) : y <• (g * h) = (y <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

theorem rsmul_one (y : X) : y <• (1 : H) = y := by rw [MulOpposite.op_one, one_smul]

theorem rsmul_inv_eq {x : X} {h : H} (hh : x <• h = x) : x <• h⁻¹ = x := by
  conv_lhs => rw [← hh]
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem rsmul_inv_smul (y : X) (h : H) : (y <• h) <• h⁻¹ = y := by
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem germ_mul {x : X} {g h : H} (hg : x <• g = x) (hh : x <• h = x) :
    germ x (g * h) = germ x g * germ x h :=
  (germEq_mul_and_germ_mul x).2 g h hg hh

theorem germ_def {x : X} {h : H} (hh : x <• h = x) :
    germ x h = QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩ := by
  unfold germ; rw [dif_pos hh]

theorem germ_one (x : X) : germ x (1 : H) = 1 := by
  rw [germ_def (rsmul_one x)]
  rfl

theorem germ_inv {x : X} {h : H} (hh : x <• h = x) : germ x h⁻¹ = (germ x h)⁻¹ := by
  have := germ_mul hh (rsmul_inv_eq hh)
  rw [mul_inv_cancel, germ_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem germ_eq_one_of_isotropy {L : Subgroup H} {x : X} (hiso : isotropy L x = ⊥) {τ : H}
    (hτ : τ ∈ L) (hx : x <• τ = x) : germ x τ = 1 := by
  rw [germ_def hx]
  have hmem : (⟨τ, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top τ, hx⟩⟩ : pointStab (⊤ : Subgroup H) x)
      ∈ (pointStab L x).subgroupOf (pointStab ⊤ x) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hτ, hx⟩
  have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (trivialNear (H := H) x)) hmem
  unfold isotropy at hiso
  rw [hiso, Subgroup.mem_bot] at this
  exact this

theorem transport_spec {L : Subgroup H} {x y : X} (h : ∃ σ ∈ L, x <• σ = y) :
    transport L x y ∈ L ∧ x <• transport L x y = y := by
  unfold transport
  exact Classical.epsilon_spec (p := fun σ => σ ∈ L ∧ x <• σ = y) (by
    obtain ⟨σ, h1, h2⟩ := h; exact ⟨σ, h1, h2⟩)

theorem exists_L_of_mem {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : ∃ σ ∈ L, x <• σ = x <• g := by
  have : x <• g ∈ rightOrbit L x := by
    rw [hL.1 x]; exact ⟨g, hg, rfl⟩
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

theorem orbit_smul {G : Subgroup H} {o x : X} (hx : x ∈ rightOrbit G o) {g : H} (hg : g ∈ G) :
    x <• g ∈ rightOrbit G o := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k * g, G.mul_mem hk hg, (rsmul_mul o k g).symm⟩

theorem exists_of_mem_isotropy {K : Subgroup H} {x : X} {γ : GermGroup (H := H) x}
    (hγ : γ ∈ isotropy K x) : ∃ h ∈ K, x <• h = x ∧ germ x h = γ := by
  obtain ⟨a, ha, rfl⟩ := hγ
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
  obtain ⟨hK, hx⟩ := Subgroup.mem_inf.mp ha
  refine ⟨a, hK, hx, ?_⟩
  rw [germ_def hx]
  rfl

end GermBase

end ErschlerZheng
end

section
/-!
# Transporting germs by conjugation (helpers for B2, B5, B6)
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermConj

open GermBase

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

set_option linter.unusedSectionVars false

theorem le_sup_L {G L : Subgroup H} {σ : H} (h : σ ∈ L) : σ ∈ G ⊔ L :=
  (le_sup_right : L ≤ G ⊔ L) h

theorem le_sup_G {G L : Subgroup H} {g : H} (h : g ∈ G) : g ∈ G ⊔ L :=
  (le_sup_left : G ≤ G ⊔ L) h

end GermConj

end ErschlerZheng
end

section
/-!
# B8: Proposition 3.3 (pp. 18–20), as a reduction to B2, B5, B6 and B7

The paper's proof. Along the walk `W_n`, the `H_o`-coset of the germ configuration `Φ_{W_n}(o)`
changes at step `n+1` exactly when `(X_{n+1}, o·W_n) ∉ ℋ` (B6's cocycle, B5's description of `τ`,
B2's description of `H_x` and `ℋ`). The expected number of changes is
`Σ_x G_{P_μ}(o, x) μ{g : (g, x) ∉ ℋ} < ∞`, so by Borel–Cantelli the coset stabilises a.s. The tail
event `A_{H_o}` ("the limit coset is `H_o`") then has probability in `(0, 1)`: translating by an
element fixing `o` permutes the cosets, and non-degeneracy gives `ℙ_1(A) ⩾ c ℙ_g(A)`. B7 concludes.
-/

open scoped RightActions ENNReal
open MeasureTheory

namespace ErschlerZheng

namespace B8Dev

open B7Dev B8MarkovDev GermBase GermConj

/-- `ξ_0 ⋯ ξ_{n-1}`. -/
def prodN {Γ : Type*} [Group Γ] (ξ : ℕ → Γ) (n : ℕ) : Γ := (List.ofFn fun i : Fin n => ξ i).prod

theorem prodN_succ {Γ : Type*} [Group Γ] (ξ : ℕ → Γ) (n : ℕ) :
    prodN ξ (n + 1) = prodN ξ n * ξ n := by
  unfold prodN
  rw [List.ofFn_succ', List.prod_concat]
  rfl

theorem prodN_cons {Γ : Type*} [Group Γ] (z : Γ) (ξ : ℕ → Γ) (n : ℕ) :
    prodN (consMap (z, ξ)) (n + 1) = z * prodN ξ n := by
  unfold prodN
  rw [List.ofFn_succ, List.prod_cons]
  rfl

theorem pathMap_eq {Γ : Type*} [Group Γ] (y : Γ) (ξ : ℕ → Γ) (n : ℕ) :
    pathMap y ξ n = y * prodN ξ n := rfl

theorem ofReal_mass_eq {Γ : Type*} {μ : Γ → ℝ} (hμ : IsProbability μ) (S : Set Γ) :
    ENNReal.ofReal (mass μ S) = ∑' g, S.indicator (fun x => ENNReal.ofReal (μ x)) g := by
  unfold mass
  rw [ENNReal.ofReal_tsum_of_nonneg (fun g => Set.indicator_nonneg (fun x _ => hμ.1 x) g)
    (hμ.2.summable.indicator S)]
  congr 1
  funext g
  by_cases hg : g ∈ S <;> simp [Set.indicator, hg]

end B8Dev

end ErschlerZheng
end

section
open scoped RightActions ENNReal
open MeasureTheory
open ErschlerZheng
open B7Dev B8MarkovDev GermBase GermConj B8Dev in
theorem solution {H : Type*} [Group H]
    {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X]
    [DecidableEq X] (G L : Subgroup H) [Countable G] (hL : IsAuxiliary (X := X) G L) (o : X)
    (hGo : isotropy (G ⊔ L) o ≠ ⊥) (hGGo : isotropy (G ⊔ L) o = isotropy G o)
    (μ : G → ℝ) (hμ : IsProbability μ) (hnd : IsNondegenerate μ)
    (o₀ : rightOrbit G o) (ho₀ : (o₀ : X) = o)
    (Ho : Subgroup (GermGroup (H := H) o)) (hHo : Ho < isotropy (G ⊔ L) o)
    (hsum : ∑' x : rightOrbit G o, MarkovChain.green (orbitKernel G μ o) o₀ x *
        ENNReal.ofReal (mass μ {g : G | ((g : H), (x : X)) ∉ germSubgroupoid G L o Ho}) < ⊤) :
    HasNontrivialPoissonBoundary μ := by
  let _ : MeasurableSpace G := ⊤
  have _ : DiscreteMeasurableSpace G := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have := isProbabilityMeasure_stepMeasure hμ
  set P := Measure.infinitePi (fun _ : ℕ => stepMeasure μ) with hP
  set ℋ := germSubgroupoid G L o Ho with hℋ
  have hoo : o ∈ rightOrbit G o := ⟨1, G.one_mem, by rw [MulOpposite.op_one, one_smul]⟩
  set Φ : G → GermGroup (H := H) o := fun g => germConfig L (g : H) o with hΦ
  have hB2 := (isSubgroup_localGermSet_and_germSubgroupoid_closed G L hL).2 o hGo Ho hHo
  have hB5 := germAction_wellDefined_and_mul G L hL o
  have hB6 := germConfig_mul_and_injective G L hL o
  -- (a) the coset changes exactly at bad steps
  have hstep : ∀ g k : G, (Φ g)⁻¹ * Φ (g * k) ∈ Ho ↔ ((k : H), o <• (g : H)) ∈ ℋ := by
    intro g k
    have hcoc := hB6.2.1 g g.2 k k.2 o hoo
    simp only [hΦ, Subgroup.coe_mul]
    rw [hcoc, inv_mul_cancel_left]
    obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL o g.2)
    set σ := transport L o (o <• (g : H))
    set x := o <• (g : H)
    have hx : x ∈ rightOrbit G o := orbit_smul hoo g.2
    obtain ⟨hσ'L, hσ'⟩ := transport_spec (exists_L_of_mem hL x k.2)
    set σ' := transport L x (x <• (k : H))
    have hh : x <• ((k : H) * σ'⁻¹) = x := by
      rw [rsmul_mul]
      exact (congrArg (fun y => y <• σ'⁻¹) hσ'.symm).trans (rsmul_inv_smul x σ')
    rw [hB5.1 g g.2 (germConfig L (k : H)) o hoo σ hσL hσ _ hh rfl]
    have hGL : (k : H) * σ'⁻¹ ∈ G ⊔ L :=
      Subgroup.mul_mem _ (le_sup_G k.2) (le_sup_L (L.inv_mem hσ'L))
    have hσo : o <• σ = x := hσ
    rw [← hB2.2.2.1 x hx σ hσL hσo _ hGL hh, hB2.2.2.2.1 k k.2 x hx σ' hσ'L hσ']
  -- (b) translation by an element fixing `o`
  have htrans : ∀ g₀ k : G, o <• (g₀ : H) = o → Φ (g₀ * k) = Φ g₀ * Φ k := by
    intro g₀ k hg₀
    simp only [hΦ, Subgroup.coe_mul]
    rw [hB6.2.1 g₀ g₀.2 k k.2 o hoo]
    congr 1
    set x := o <• (g₀ : H)
    obtain ⟨hσ'L, hσ'⟩ := transport_spec (exists_L_of_mem hL x k.2)
    have hh : x <• ((k : H) * (transport L x (x <• (k : H)))⁻¹) = x := by
      rw [rsmul_mul]
      exact (congrArg (fun y => y <• (transport L x (x <• (k : H)))⁻¹) hσ'.symm).trans
        (rsmul_inv_smul x _)
    rw [hB5.1 g₀ g₀.2 (germConfig L (k : H)) o hoo 1 L.one_mem (by
      rw [MulOpposite.op_one, one_smul]; exact hg₀.symm) _ hh rfl, one_mul, inv_one, mul_one]
    unfold germConfig
    simp only [x, hg₀]
  -- the events
  set A : GermGroup (H := H) o → Set (ℕ → G) :=
    fun γ => {w | ∀ᶠ n in Filter.atTop, γ⁻¹ * Φ (w n) ∈ Ho} with hA
  have hAmeas : ∀ γ, MeasurableSet (A γ) := by
    intro γ
    have : A γ = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), (fun w : ℕ → G => w n) ⁻¹'
        {g | γ⁻¹ * Φ g ∈ Ho} := by
      ext w; simp [hA, Filter.eventually_atTop]
    rw [this]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter
      fun _ => measurable_pi_apply n (DiscreteMeasurableSpace.forall_measurableSet _)
  have hAinv : ∀ γ, IsShiftInvariant (A γ) := by
    intro γ
    ext w
    simp only [hA, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
      exact Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => by
        have := hN (n - 1) (by omega); rwa [show n - 1 + 1 = n by omega] at this⟩
    · intro h
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
      exact Filter.eventually_atTop.mpr ⟨N, fun n hn => hN (n + 1) (by omega)⟩
  -- translation of the events
  have hAtrans : ∀ (g₀ : G) (γ : GermGroup (H := H) o), o <• (g₀ : H) = o →
      pathMap g₀ ⁻¹' A γ = pathMap 1 ⁻¹' A ((Φ g₀)⁻¹ * γ) := by
    intro g₀ γ hg₀
    ext ξ
    simp only [hA, Set.mem_preimage, Set.mem_ofPred_eq, pathMap_eq, one_mul]
    have e : ∀ n, γ⁻¹ * Φ (g₀ * prodN ξ n) = ((Φ g₀)⁻¹ * γ)⁻¹ * Φ (prodN ξ n) := by
      intro n; rw [htrans g₀ (prodN ξ n) hg₀]; group
    simp only [e]
  -- (d) harmonicity and the lower bound along the semigroup
  have hharm : ∀ (B : Set (ℕ → G)), MeasurableSet B → IsShiftInvariant B → ∀ y : G,
      P (pathMap y ⁻¹' B) = ∑' z, ENNReal.ofReal (μ z) * P (pathMap (y * z) ⁻¹' B) := by
    intro B hB hBinv y
    have key : P (pathMap y ⁻¹' B) =
        ∑' z, ENNReal.ofReal (μ z) * P {ξ | consMap (z, ξ) ∈ pathMap y ⁻¹' B} :=
      measure_eq_tsum hμ (measurable_pathMap y hB)
    rw [key]
    congr 1; funext z
    congr 2
    ext ξ
    exact cons_mem_path hBinv y z ξ
  have hlower : ∀ (B : Set (ℕ → G)), MeasurableSet B → IsShiftInvariant B → ∀ g : G,
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y : G, c * P (pathMap (y * g) ⁻¹' B) ≤ P (pathMap y ⁻¹' B) := by
    intro B hB hBinv g
    have hg : g ∈ Subsemigroup.closure {g | μ g ≠ 0} := by rw [hnd]; trivial
    induction hg using Subsemigroup.closure_induction with
    | mem z hz =>
      refine ⟨ENNReal.ofReal (μ z), (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (hμ.1 z)
        (Ne.symm hz))).ne', fun y => ?_⟩
      rw [hharm B hB hBinv y]
      exact ENNReal.le_tsum z
    | mul a b _ _ iha ihb =>
      obtain ⟨c₁, hc₁, h₁⟩ := iha
      obtain ⟨c₂, hc₂, h₂⟩ := ihb
      refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun y => ?_⟩
      calc c₁ * c₂ * P (pathMap (y * (a * b)) ⁻¹' B)
          = c₁ * (c₂ * P (pathMap (y * a * b) ⁻¹' B)) := by rw [mul_assoc, mul_assoc]
        _ ≤ c₁ * P (pathMap (y * a) ⁻¹' B) := by gcongr; exact h₂ (y * a)
        _ ≤ P (pathMap y ⁻¹' B) := h₁ y
  -- (e) Borel–Cantelli
  set bad : rightOrbit G o → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (mass μ {g : G | ((g : H), (x : X)) ∉ ℋ}) with hbad
  set E : rightOrbit G o → ℕ → Set (ℕ → G) := fun y n =>
    {ξ | ((ξ n : H), (y : X) <• ((prodN ξ n : G) : H)) ∉ ℋ} with hE
  have hEmeas : ∀ y n, MeasurableSet (E y n) := by
    intro y n
    have h1 : Measurable fun ξ : ℕ → G => (ξ n, prodN ξ n) := by
      refine Measurable.prodMk (measurable_pi_apply n) ?_
      have h2 : Measurable fun ξ : ℕ → G => fun i : Fin n => ξ i :=
        measurable_pi_lambda _ fun i => measurable_pi_apply _
      exact (measurable_of_countable (fun u : Fin n → G => (List.ofFn u).prod)).comp h2
    show MeasurableSet ((fun ξ : ℕ → G => (ξ n, prodN ξ n)) ⁻¹'
      {p : G × G | ((p.1 : H), (y : X) <• ((p.2 : G) : H)) ∉ ℋ})
    exact h1 (Set.to_countable _).measurableSet
  have hEsum : ∀ n (y : rightOrbit G o), P (E y n) =
      ∑' x, ENNReal.ofReal (DurrettProbability.stepProb (orbitKernel G μ o) n y x) * bad x := by
    intro n
    induction n with
    | zero =>
      intro y
      have key : P (E y 0) = ∑' z, ENNReal.ofReal (μ z) * P {ξ | consMap (z, ξ) ∈ E y 0} :=
        measure_eq_tsum hμ (hEmeas y 0)
      rw [key]
      rw [tsum_eq_single y (fun x hx => by
        simp [DurrettProbability.stepProb, Ne.symm hx])]
      simp only [DurrettProbability.stepProb, if_true, ENNReal.ofReal_one, one_mul, hbad]
      rw [ofReal_mass_eq hμ]
      congr 1; funext z
      by_cases hz : ((z : H), (y : X)) ∈ ℋ
      · have : {ξ : ℕ → G | consMap (z, ξ) ∈ E y 0} = ∅ := by
          ext ξ; simp [hE, consMap, prodN, hz]
        simp [this, Set.indicator, hz]
      · have : {ξ : ℕ → G | consMap (z, ξ) ∈ E y 0} = Set.univ := by
          ext ξ; simp [hE, consMap, prodN, hz]
        simp [this, Set.indicator, hz]
    | succ n ih =>
      intro y
      have key : P (E y (n + 1)) =
          ∑' z, ENNReal.ofReal (μ z) * P {ξ | consMap (z, ξ) ∈ E y (n + 1)} :=
        measure_eq_tsum hμ (hEmeas y (n + 1))
      rw [key]
      have hset : ∀ z : G, {ξ : ℕ → G | consMap (z, ξ) ∈ E y (n + 1)} = E (oact y z) n := by
        intro z
        ext ξ
        show (((consMap (z, ξ) (n + 1) : G) : H),
            (y : X) <• ((prodN (consMap (z, ξ)) (n + 1) : G) : H)) ∉ ℋ ↔
          (((ξ n : G) : H), ((y : X) <• (z : H)) <• ((prodN ξ n : G) : H)) ∉ ℋ
        rw [prodN_cons, Subgroup.coe_mul, rsmul_mul]
        rfl
      simp_rw [hset]
      simp_rw [ih]
      have hm : ∀ z : G, ENNReal.ofReal (μ z) * ∑' x, ENNReal.ofReal
          (DurrettProbability.stepProb (orbitKernel G μ o) n (oact y z) x) * bad x =
          ∑' x, ENNReal.ofReal (μ z) * (ENNReal.ofReal
          (DurrettProbability.stepProb (orbitKernel G μ o) n (oact y z) x) * bad x) :=
        fun z => ENNReal.tsum_mul_left.symm
      simp_rw [hm]
      rw [ENNReal.tsum_comm]
      congr 1; funext x
      rw [(stepProb_spec G hμ o n y x).2.2, ← ENNReal.tsum_mul_right]
      congr 1; funext z; ring
  have hBC : ∑' n, P (E o₀ n) ≠ ⊤ := by
    simp_rw [hEsum]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right]
    exact hsum.ne
  have hae := ae_eventually_notMem hBC
  -- (f) stabilisation
  have hstab : ∀ᵐ ξ ∂P, ∃ g : G, pathMap 1 ξ ∈ A (Φ g) := by
    filter_upwards [hae] with ξ hξ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hξ
    refine ⟨prodN ξ N, Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
    simp only [pathMap_eq, one_mul]
    induction n, hn using Nat.le_induction with
    | base => rw [inv_mul_cancel (Φ (prodN ξ N))]; exact Ho.one_mem
    | succ n hn ih =>
      have hgood := hN n hn
      simp only [hE, Set.mem_ofPred_eq, not_not, ho₀] at hgood
      rw [prodN_succ]
      have := (hstep (prodN ξ n) (ξ n)).mpr hgood
      have e : (Φ (prodN ξ N))⁻¹ * Φ (prodN ξ n * ξ n) =
          ((Φ (prodN ξ N))⁻¹ * Φ (prodN ξ n)) * ((Φ (prodN ξ n))⁻¹ * Φ (prodN ξ n * ξ n)) := by
        group
      rw [e]
      exact Ho.mul_mem ih this
  have hpos1 : ∃ g₁ : G, P (pathMap 1 ⁻¹' A (Φ g₁)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : P (⋃ g : G, pathMap 1 ⁻¹' A (Φ g)) = 0 := measure_iUnion_null hcon
    have h1 : P (⋃ g : G, pathMap 1 ⁻¹' A (Φ g))ᶜ = 0 := by
      have := ae_iff.mp hstab
      convert this using 2
      ext ξ; simp
    have := measure_union_le (μ := P) (⋃ g : G, pathMap 1 ⁻¹' A (Φ g))
      (⋃ g : G, pathMap 1 ⁻¹' A (Φ g))ᶜ
    rw [Set.union_compl_self, measure_univ, h0, h1, add_zero] at this
    exact absurd this (by norm_num)
  obtain ⟨g₁, hg₁⟩ := hpos1
  have hΦmem : ∀ g : G, Φ g ∈ isotropy (G ⊔ L) o := fun g => hB6.1 g g.2 o hoo
  -- germs of `Ĝ_o = 𝒢_o` are germ configurations of elements fixing `o`
  have hrealize : ∀ γ ∈ isotropy (G ⊔ L) o, ∃ g : G, o <• (g : H) = o ∧ Φ g = γ := by
    intro γ hγ
    rw [hGGo] at hγ
    obtain ⟨h, hhG, hho, rfl⟩ := exists_of_mem_isotropy hγ
    refine ⟨⟨h, hhG⟩, hho, ?_⟩
    simp only [hΦ]
    unfold germConfig
    obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL o hhG)
    have hσo : o <• transport L o (o <• h) = o := hσ.trans hho
    have h1 : germ o (transport L o (o <• h))⁻¹ = 1 := by
      rw [germ_inv hσo, germ_eq_one_of_isotropy (hL.2 o) hσL hσo, inv_one]
    rw [germ_mul hho (rsmul_inv_eq hσo), h1, mul_one]
  -- `ℙ_1(A_{H_o}) > 0`
  obtain ⟨g₀, hg₀o, hg₀Φ⟩ := hrealize (Φ g₁)⁻¹ (Subgroup.inv_mem _ (hΦmem g₁))
  have hP0 : P (pathMap g₀ ⁻¹' A 1) ≠ 0 := by
    rw [hAtrans g₀ 1 hg₀o, hg₀Φ, inv_inv, mul_one]
    exact hg₁
  obtain ⟨c, hc, hcle⟩ := hlower (A 1) (hAmeas 1) (hAinv 1) g₀
  have hpos : 0 < P (pathMap 1 ⁻¹' A 1) := by
    have := hcle 1
    rw [one_mul] at this
    exact lt_of_lt_of_le (ENNReal.mul_pos hc hP0) this
  -- `ℙ_1(A_{H_o}) < 1`
  obtain ⟨γ, hγ, hγHo⟩ := SetLike.exists_of_lt hHo
  obtain ⟨g, hgo, hgΦ⟩ := hrealize γ hγ
  have hPγ : P (pathMap g ⁻¹' A γ) = P (pathMap 1 ⁻¹' A 1) := by
    rw [hAtrans g γ hgo, hgΦ, inv_mul_cancel]
  obtain ⟨c', hc', hc'le⟩ := hlower (A γ) (hAmeas γ) (hAinv γ) g
  have hposγ : 0 < P (pathMap 1 ⁻¹' A γ) := by
    have := hc'le 1
    rw [one_mul, hPγ] at this
    exact lt_of_lt_of_le (ENNReal.mul_pos hc' hpos.ne') this
  have hdisj : Disjoint (pathMap 1 ⁻¹' A 1) (pathMap 1 ⁻¹' A γ) := by
    rw [Set.disjoint_left]
    intro ξ h1 h2
    simp only [hA, Set.mem_preimage, Set.mem_ofPred_eq, inv_one, one_mul] at h1 h2
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    apply hγHo
    have := Ho.mul_mem hn1 (Ho.inv_mem hn2)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  have hsumle : P (pathMap 1 ⁻¹' A 1) + P (pathMap 1 ⁻¹' A γ) ≤ 1 := by
    rw [← measure_union hdisj (measurable_pathMap 1 (hAmeas γ))]
    exact prob_le_one
  have hlt : P (pathMap 1 ⁻¹' A 1) < 1 := by
    by_contra hge
    push Not at hge
    have := ENNReal.lt_add_right ENNReal.one_ne_top hposγ.ne'
    have h2 : 1 + P (pathMap 1 ⁻¹' A γ) ≤ 1 := by
      calc 1 + P (pathMap 1 ⁻¹' A γ) ≤ P (pathMap 1 ⁻¹' A 1) + P (pathMap 1 ⁻¹' A γ) := by
            gcongr
        _ ≤ 1 := hsumle
    exact absurd (lt_of_lt_of_le this h2) (lt_irrefl _)
  have hmap : pathMeasure μ 1 (A 1) = P (pathMap 1 ⁻¹' A 1) := by
    show (Measure.map (pathMap 1) P) (A 1) = _
    rw [Measure.map_apply (measurable_pathMap 1) (hAmeas 1)]
  exact (KaimanovichVershik.hasNontrivialPoissonBoundary_iff_exists_isShiftInvariant_pathMeasure_pos_lt_one
    μ hμ).mpr ⟨A 1, hAmeas 1, hAinv 1, 1, hmap ▸ hpos, hmap ▸ hlt⟩
end
