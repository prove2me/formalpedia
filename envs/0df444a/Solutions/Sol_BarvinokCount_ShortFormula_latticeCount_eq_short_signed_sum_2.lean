-- Prove2me | solution 2 for BarvinokCount.ShortFormula.latticeCount_eq_short_signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T21:15:20.182988+00:00
-- url     : https://prove2.me/submissions/154fea63-7c3c-4071-9811-18a08de4a477

-- Complete checked reconstruction of the native Barvinok short signed formula.
-- Licensed under Apache 2.0.
import Definitions.Def_BarvinokCount_ShortFormula_coneIndex
import Definitions.Def_BarvinokCount_ShortFormula_integralSimplex
import Definitions.Def_BarvinokCount_ShortFormula_iterCount
import Definitions.Def_BarvinokCount_ShortFormula_sigma
import Mathlib


-- Begin ConeTerms

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

structure ConeTerm (d : ℕ) where
  dim : ℕ
  gens : Fin dim → Fin d → ℤ
  coeff : ℤ

noncomputable def ConeTerm.eval {d : ℕ} (q : ConeTerm d) (x : Fin d → ℝ) : ℝ :=
  (q.coeff:ℝ)*(cone q.gens).indicator (fun _=>1) x
noncomputable def ConeTerm.sigmaEval {d : ℕ} (q : ConeTerm d) (c : Fin d → ℝ) : ℝ :=
  (q.coeff:ℝ)*sigma q.gens c

def ConeTerm.scale {d : ℕ} (r : ℤ) (q : ConeTerm d) : ConeTerm d :=
  ⟨q.dim,q.gens,r*q.coeff⟩

lemma ConeTerm.eval_scale {d : ℕ} (r : ℤ) (q : ConeTerm d) (x : Fin d → ℝ) :
    (q.scale r).eval x=(r:ℝ)*q.eval x := by simp [eval,scale,mul_assoc]
lemma ConeTerm.sigmaEval_scale {d : ℕ} (r : ℤ) (q : ConeTerm d) (c : Fin d → ℝ) :
    (q.scale r).sigmaEval c=(r:ℝ)*q.sigmaEval c := by simp [sigmaEval,scale,mul_assoc]

noncomputable def coneTermSum {d : ℕ} (L : List (ConeTerm d)) (x : Fin d → ℝ) : ℝ :=
  (L.map (fun q=>q.eval x)).sum
noncomputable def sigmaTermSum {d : ℕ} (L : List (ConeTerm d)) (c : Fin d → ℝ) : ℝ :=
  (L.map (fun q=>q.sigmaEval c)).sum

def ListPrimitive {d : ℕ} (L : List (ConeTerm d)) : Prop := ∀ q∈L,IsPrimitiveGens q.gens
def ListRegular {d : ℕ} (L : List (ConeTerm d)) (c : Fin d → ℝ) : Prop :=
  ∀ q∈L,IsRegular q.gens c

lemma coneTermSum_append {d : ℕ} (L M : List (ConeTerm d)) (x : Fin d → ℝ) :
    coneTermSum (L++M) x=coneTermSum L x+coneTermSum M x := by simp [coneTermSum]
lemma sigmaTermSum_append {d : ℕ} (L M : List (ConeTerm d)) (c : Fin d → ℝ) :
    sigmaTermSum (L++M) c=sigmaTermSum L c+sigmaTermSum M c := by simp [sigmaTermSum]

lemma coneTermSum_scale {d : ℕ} (L : List (ConeTerm d)) (r : ℤ) (x : Fin d → ℝ) :
    coneTermSum (L.map (fun q=>q.scale r)) x=(r:ℝ)*coneTermSum L x := by
  induction L with
  | nil => simp [coneTermSum]
  | cons q L ih => simpa [coneTermSum,ConeTerm.eval_scale,mul_add] using ih
lemma sigmaTermSum_scale {d : ℕ} (L : List (ConeTerm d)) (r : ℤ) (c : Fin d → ℝ) :
    sigmaTermSum (L.map (fun q=>q.scale r)) c=(r:ℝ)*sigmaTermSum L c := by
  induction L with
  | nil => simp [sigmaTermSum]
  | cons q L ih => simpa [sigmaTermSum,ConeTerm.sigmaEval_scale,mul_add] using ih

end BarvinokCount.ShortFormula.Proof
-- End ConeTerms

-- Begin LatticeBasic

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof

@[simp] theorem castVec_zero {d : ℕ} : castVec (0 : Fin d → ℤ) = 0 := by ext i; simp [castVec]
@[simp] theorem castVec_add {d : ℕ} (x y : Fin d → ℤ) :
    castVec (x+y) = castVec x + castVec y := by ext i; simp [castVec]
@[simp] theorem castVec_sub {d : ℕ} (x y : Fin d → ℤ) :
    castVec (x-y) = castVec x - castVec y := by ext i; simp [castVec]
@[simp] theorem castVec_zsmul {d : ℕ} (m : ℤ) (x : Fin d → ℤ) :
    castVec (m • x) = (m:ℝ) • castVec x := by ext i; simp [castVec]
@[simp] theorem castVec_sum {d : ℕ} {I : Type*} (s : Finset I) (u : I → Fin d → ℤ) :
    castVec (∑ i ∈ s, u i) = ∑ i ∈ s, castVec (u i) := by
  ext j
  simp [castVec]

theorem castVec_injective {d : ℕ} : Function.Injective (@castVec d) := by
  intro x y h
  ext i
  have hi : (x i : ℝ) = (y i : ℝ) := congrFun h i
  exact_mod_cast hi

theorem simple_sum_injective {d k : ℕ} {u : Fin k → Fin d → ℤ}
    (hu : IsSimpleGens u) {a b : Fin k → ℝ}
    (h : ∑ i, a i • castVec (u i) = ∑ i, b i • castVec (u i)) : a=b := by
  exact (linearIndependent_iff_injective_fintypeLinearCombination.mp hu) h

theorem zero_mem_halfOpenBox {d k : ℕ} (u : Fin k → Fin d → ℤ) :
    (0 : Fin d → ℝ) ∈ halfOpenBox u := by
  exact ⟨0, by simp, by simp⟩

theorem halfOpenBox_subset_span {d k : ℕ} (u : Fin k → Fin d → ℤ) :
    halfOpenBox u ⊆ Submodule.span ℝ (Set.range fun i => castVec (u i)) := by
  rintro x ⟨a,ha,rfl⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

end BarvinokCount.ShortFormula.Proof
-- End LatticeBasic

-- Begin BoxFinite

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof

theorem abs_le_supNorm {d : ℕ} (u : Fin d → ℤ) (j : Fin d) : |u j| ≤ (supNorm u : ℤ) := by
  have h : (u j).natAbs ≤ supNorm u := Finset.le_sup (f := fun i => (u i).natAbs) (Finset.mem_univ j)
  simpa only [Int.natCast_natAbs] using (show ((u j).natAbs : ℤ) ≤ (supNorm u : ℤ) by exact_mod_cast h)

theorem box_coordinate_bound {d k : ℕ} (u : Fin k → Fin d → ℤ)
    {z : Fin d → ℤ} (hz : castVec z ∈ halfOpenBox u) (j : Fin d) :
    |z j| ≤ ((∑ i, supNorm (u i) : ℕ) : ℤ) := by
  obtain ⟨a,ha,he⟩ := hz
  have he' : (z j : ℝ) = ∑ i, a i * (u i j : ℝ) := by
    simpa [castVec] using congrFun he j
  have hh : |(z j : ℝ)| ≤ ∑ i, (supNorm (u i) : ℝ) := by
    rw [he']
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul, abs_of_nonneg (ha i).1]
    calc
      a i * |(u i j : ℝ)| ≤ 1 * |(u i j : ℝ)| :=
        mul_le_mul_of_nonneg_right (ha i).2.le (abs_nonneg _)
      _ ≤ (supNorm (u i) : ℝ) := by
        simpa using (show |(u i j : ℝ)| ≤ (supNorm (u i) : ℝ) by exact_mod_cast abs_le_supNorm (u i) j)
  exact_mod_cast hh

theorem finite_box_lattice {d k : ℕ} (u : Fin k → Fin d → ℤ) :
    {z : Fin d → ℤ | castVec z ∈ halfOpenBox u}.Finite := by
  let M : ℤ := ∑ i, (supNorm (u i) : ℤ)
  have hf : (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-M) M)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  apply hf.subset
  intro z hz j hj
  exact abs_le.mp (by simpa [M] using box_coordinate_bound u hz j)

theorem coneIndex_pos {d k : ℕ} (u : Fin k → Fin d → ℤ) : 0 < coneIndex u := by
  let : Finite {z : Fin d → ℤ // castVec z ∈ halfOpenBox u} := (finite_box_lattice u).to_subtype
  let : Nonempty {z : Fin d → ℤ // castVec z ∈ halfOpenBox u} :=
    ⟨⟨0, by simpa using zero_mem_halfOpenBox u⟩⟩
  exact Nat.card_pos

end BarvinokCount.ShortFormula.Proof
-- End BoxFinite

-- Begin SigmaAnalytic

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

noncomputable def sigmaNumerator (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) : ℝ :=
  ∑ z ∈ (finite_box_lattice u).toFinset, Real.exp (c ⬝ᵥ castVec z)
noncomputable def sigmaDenominator (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) : ℝ :=
  ∏ i,(1-Real.exp (c ⬝ᵥ castVec (u i)))

lemma sigma_fraction (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) :
    sigma u c=sigmaNumerator u c / sigmaDenominator u c := by
  rw [sigma,finsum_mem_eq_finite_toFinset_sum _ (finite_box_lattice u)]
  simp only [sigmaNumerator,sigmaDenominator,div_eq_mul_inv,one_mul,Finset.prod_inv_distrib]

lemma sigmaDenominator_ne_zero (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ)
    (hc : IsRegular u c) : sigmaDenominator u c≠0 := by
  unfold sigmaDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [sub_ne_zero]
  exact fun he=>hc i (Real.exp_injective (by simpa using he.symm))

lemma analytic_dot_exp (z : Fin d → ℝ) (c : Fin d → ℝ) :
    AnalyticAt ℝ (fun x : Fin d → ℝ => Real.exp (x ⬝ᵥ z)) c := by
  have ha := ((dotProductBilin ℝ ℝ z).toContinuousLinearMap).analyticAt c
  change AnalyticAt ℝ (fun x : Fin d → ℝ => z ⬝ᵥ x) c at ha
  have hb : AnalyticAt ℝ (fun x : Fin d → ℝ => x ⬝ᵥ z) c := by
    simpa only [dotProduct_comm] using ha
  exact hb.rexp'

lemma sigmaNumerator_analytic (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) :
    AnalyticAt ℝ (sigmaNumerator u) c := by
  unfold sigmaNumerator
  apply Finset.analyticAt_fun_sum
  intro z _
  exact analytic_dot_exp (castVec z) c

lemma sigmaDenominator_analytic (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) :
    AnalyticAt ℝ (sigmaDenominator u) c := by
  unfold sigmaDenominator
  apply Finset.analyticAt_fun_prod
  intro i _
  exact analyticAt_const.sub (analytic_dot_exp (castVec (u i)) c)

end BarvinokCount.ShortFormula.Proof
-- End SigmaAnalytic

-- Begin SigmaClear

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d : ℕ}

noncomputable def listDenominator : List (ConeTerm d) → (Fin d → ℝ) → ℝ
  | [],_ => 1
  | q::L,c => sigmaDenominator q.gens c * listDenominator L c
noncomputable def listNumerator : List (ConeTerm d) → (Fin d → ℝ) → ℝ
  | [],_ => 0
  | q::L,c => (q.coeff:ℝ)*sigmaNumerator q.gens c*listDenominator L c +
      sigmaDenominator q.gens c*listNumerator L c

lemma listDenominator_ne_zero (L : List (ConeTerm d)) (c : Fin d → ℝ) (hc : ListRegular L c) :
    listDenominator L c≠0 := by
  induction L with
  | nil => exact one_ne_zero
  | cons q L ih =>
    exact mul_ne_zero (sigmaDenominator_ne_zero q.gens c (hc q (by simp)))
      (ih (fun r hr=>hc r (by simp [hr])))

lemma sigmaTermSum_fraction (L : List (ConeTerm d)) (c : Fin d → ℝ) (hc : ListRegular L c) :
    sigmaTermSum L c=listNumerator L c/listDenominator L c := by
  induction L with
  | nil => simp [sigmaTermSum,listNumerator,listDenominator]
  | cons q L ih =>
    have hq := sigmaDenominator_ne_zero q.gens c (hc q (by simp))
    have ht : ListRegular L c := fun r hr=>hc r (by simp [hr])
    have hL := listDenominator_ne_zero L c ht
    change (q.coeff:ℝ)*sigma q.gens c+sigmaTermSum L c=_
    rw [sigma_fraction,ih ht]
    simp only [listNumerator,listDenominator]
    field_simp

lemma listDenominator_analytic (L : List (ConeTerm d)) (c : Fin d → ℝ) :
    AnalyticAt ℝ (listDenominator L) c := by
  induction L with
  | nil => exact analyticAt_const
  | cons q L ih => exact (sigmaDenominator_analytic q.gens c).mul ih

lemma listNumerator_analytic (L : List (ConeTerm d)) (c : Fin d → ℝ) :
    AnalyticAt ℝ (listNumerator L) c := by
  induction L with
  | nil => exact analyticAt_const
  | cons q L ih => exact ((analyticAt_const.mul (sigmaNumerator_analytic q.gens c)).mul
      (listDenominator_analytic L c)).add ((sigmaDenominator_analytic q.gens c).mul ih)

lemma sigmaTermSum_global_of_local (L M : List (ConeTerm d)) (c₀ : Fin d → ℝ)
    (hreg : ∀ᶠ c in 𝓝 c₀,ListRegular L c ∧ ListRegular M c)
    (he : ∀ᶠ c in 𝓝 c₀,sigmaTermSum L c=sigmaTermSum M c)
    (c : Fin d → ℝ) (hL : ListRegular L c) (hM : ListRegular M c) :
    sigmaTermSum L c=sigmaTermSum M c := by
  have hf : AnalyticOnNhd ℝ (fun c=>listNumerator L c*listDenominator M c) Set.univ :=
    fun c _=>(listNumerator_analytic L c).mul (listDenominator_analytic M c)
  have hg : AnalyticOnNhd ℝ (fun c=>listNumerator M c*listDenominator L c) Set.univ :=
    fun c _=>(listNumerator_analytic M c).mul (listDenominator_analytic L c)
  have hh : (fun c=>listNumerator L c*listDenominator M c) =ᶠ[𝓝 c₀]
      (fun c=>listNumerator M c*listDenominator L c) := by
    filter_upwards [hreg,he] with c hc he
    rw [sigmaTermSum_fraction L c hc.1,sigmaTermSum_fraction M c hc.2] at he
    exact (div_eq_div_iff (listDenominator_ne_zero L c hc.1)
      (listDenominator_ne_zero M c hc.2)).mp he
  have hall := congrFun (hf.eq_of_eventuallyEq hg hh) c
  rw [sigmaTermSum_fraction L c hL,sigmaTermSum_fraction M c hM]
  exact (div_eq_div_iff (listDenominator_ne_zero L c hL)
    (listDenominator_ne_zero M c hM)).mpr hall

end BarvinokCount.ShortFormula.Proof
-- End SigmaClear

-- Begin ConeLatticeSplit

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma cone_lattice_split (u : Fin k → Fin d → ℤ) (z : Fin d → ℤ)
    (hz : castVec z∈cone u) :
    ∃ r : Fin d → ℤ, castVec r∈halfOpenBox u ∧
      ∃ m : Fin k → ℕ, z=r+∑ i,(m i:ℤ) • u i := by
  obtain ⟨a,ha,he⟩ := hz
  let m : Fin k → ℕ := fun i=>⌊a i⌋₊
  let r := z-∑ i,(m i:ℤ) • u i
  have hr : castVec r=∑ i,(a i-(m i:ℝ)) • castVec (u i) := by
    dsimp [r]
    rw [castVec_sub,castVec_sum,he]
    simp only [castVec_zsmul,Int.cast_natCast,sub_smul,Finset.sum_sub_distrib]
  refine ⟨r,⟨fun i=>a i-m i,?_,hr⟩,m,?_⟩
  · intro i
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le (ha i))
    · have h := Nat.lt_floor_add_one (a i)
      dsimp [m]
      linarith
  · dsimp [r]
    abel

lemma cone_lattice_join (u : Fin k → Fin d → ℤ) (r : Fin d → ℤ)
    (hr : castVec r∈halfOpenBox u) (m : Fin k → ℕ) :
    castVec (r+∑ i,(m i:ℤ) • u i)∈cone u := by
  obtain ⟨a,ha,he⟩ := hr
  refine ⟨fun i=>a i+m i,fun i=>add_nonneg (ha i).1 (Nat.cast_nonneg _),?_⟩
  rw [castVec_add,castVec_sum,he]
  simp only [castVec_zsmul,Int.cast_natCast,add_smul,Finset.sum_add_distrib]

lemma cone_lattice_split_unique (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (r s : Fin d → ℤ) (hr : castVec r∈halfOpenBox u) (hs : castVec s∈halfOpenBox u)
    (m n : Fin k → ℕ) (he : r+∑ i,(m i:ℤ) • u i=s+∑ i,(n i:ℤ) • u i) :
    r=s ∧ m=n := by
  obtain ⟨a,ha,hra⟩ := hr
  obtain ⟨b,hb,hsb⟩ := hs
  have h := congrArg castVec he
  simp only [castVec_add,castVec_sum,castVec_zsmul,Int.cast_natCast,hra,hsb] at h
  have hc : (fun i=>a i+(m i:ℝ))=(fun i=>b i+(n i:ℝ)) := by
    apply simple_sum_injective hu
    simpa only [add_smul,Finset.sum_add_distrib] using h
  have hmn : m=n := by
    funext i
    have hi := congrFun hc i
    have hab := ha i
    have hbb := hb i
    have hlt : (m i : ℝ) < (n i : ℝ) + 1 := by linarith
    have hlt' : (n i : ℝ) < (m i : ℝ) + 1 := by linarith
    have hle : m i < n i + 1 := by exact_mod_cast hlt
    have hle' : n i < m i + 1 := by exact_mod_cast hlt'
    omega
  refine ⟨?_,hmn⟩
  rw [hmn] at he
  exact add_right_cancel he

end BarvinokCount.ShortFormula.Proof
-- End ConeLatticeSplit

-- Begin ConeLatticeEquiv

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

def coneLatticeJoin (u : Fin k → Fin d → ℤ) :
    ({r : Fin d → ℤ // castVec r∈halfOpenBox u} × (Fin k → ℕ)) →
      {z : Fin d → ℤ // castVec z∈cone u} :=
  fun p=>⟨p.1.val+∑ i,(p.2 i:ℤ) • u i,cone_lattice_join u p.1.val p.1.property p.2⟩

lemma coneLatticeJoin_bijective (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    Function.Bijective (coneLatticeJoin u) := by
  constructor
  · rintro ⟨r,m⟩ ⟨s,n⟩ he
    obtain ⟨hr,hm⟩ := cone_lattice_split_unique u hu r.val s.val r.property s.property m n
      (congrArg Subtype.val he)
    exact Prod.ext (Subtype.ext hr) hm
  · intro z
    obtain ⟨r,hr,m,he⟩ := cone_lattice_split u z.val z.property
    exact ⟨(⟨r,hr⟩,m),Subtype.ext he.symm⟩

noncomputable def coneLatticeEquiv (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    ({r : Fin d → ℤ // castVec r∈halfOpenBox u} × (Fin k → ℕ)) ≃
      {z : Fin d → ℤ // castVec z∈cone u} :=
  Equiv.ofBijective (coneLatticeJoin u) (coneLatticeJoin_bijective u hu)

lemma exp_coneLatticeEquiv (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (c : Fin d → ℝ) (p : {r : Fin d → ℤ // castVec r∈halfOpenBox u} × (Fin k → ℕ)) :
    Real.exp (c ⬝ᵥ castVec (coneLatticeEquiv u hu p).val)=
      Real.exp (c ⬝ᵥ castVec p.1.val) * ∏ i,(Real.exp (c ⬝ᵥ castVec (u i)))^(p.2 i) := by
  change Real.exp (c ⬝ᵥ castVec (p.1.val+∑ i,(p.2 i:ℤ) • u i))=_
  simp only [castVec_add,castVec_sum,castVec_zsmul,Int.cast_natCast,dotProduct_add,
    dotProduct_sum,dotProduct_smul,smul_eq_mul,Real.exp_add,Real.exp_sum,Real.exp_nat_mul]

end BarvinokCount.ShortFormula.Proof
-- End ConeLatticeEquiv

-- Begin GeometricProduct

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

lemma hasSum_mul_nonnegative {A B : Type*} {f : A → ℝ} {g : B → ℝ} {s t : ℝ}
    (hf : HasSum f s) (hg : HasSum g t) (hfn : ∀ a,0≤f a) (hgn : ∀ b,0≤g b) :
    HasSum (fun p : A × B => f p.1*g p.2) (s*t) := by
  have hs : Summable (fun p : A × B => f p.1*g p.2) :=
    Summable.mul_of_nonneg (f := f) (g := g) hf.summable hg.summable hfn hgn
  exact HasSum.mul hf hg hs

lemma hasSum_geometric_product (k : ℕ) (q : Fin k → ℝ)
    (hq : ∀ i,0≤q i ∧ q i<1) :
    HasSum (fun m : Fin k → ℕ => ∏ i,q i^(m i)) (∏ i,(1-q i)⁻¹) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h0 := hasSum_geometric_of_lt_one (hq 0).1 (hq 0).2
    have ht := ih (fun i=>q i.succ) (fun i=>hq i.succ)
    have h0n : ∀ n : ℕ, 0 ≤ (q 0)^n := fun n=>pow_nonneg (hq 0).1 n
    have htn : ∀ m : Fin k → ℕ, 0 ≤ ∏ i,(q i.succ)^(m i) :=
      fun m=>Finset.prod_nonneg (fun i _=>pow_nonneg (hq i.succ).1 (m i))
    have hp := hasSum_mul_nonnegative h0 ht h0n htn
    rw [← (Fin.consEquiv (fun _ : Fin (k+1)=>ℕ)).hasSum_iff] 
    simpa only [Function.comp_def,Fin.prod_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ] using hp

end BarvinokCount.ShortFormula.Proof
-- End GeometricProduct

-- Begin SigmaSeries

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma sigma_eq_box_sum (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) :
    sigma u c = (∑' r : {r : Fin d → ℤ // castVec r∈halfOpenBox u},
      Real.exp (c ⬝ᵥ castVec r.val)) * ∏ i,(1-Real.exp (c ⬝ᵥ castVec (u i)))⁻¹ := by
  let : Finite ↑({z : Fin d → ℤ | castVec z∈halfOpenBox u} : Set (Fin d → ℤ)) :=
    (finite_box_lattice u).to_subtype
  rw [sigma,← finsum_set_coe_eq_finsum_mem,← tsum_eq_finsum (L := SummationFilter.unconditional _) (Set.toFinite _)]
  simp only [one_div]
  rfl

lemma hasSum_sigma (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (c : Fin d → ℝ) (hc : ∀ i,c ⬝ᵥ castVec (u i)<0) :
    HasSum (fun z : {z : Fin d → ℤ // castVec z∈cone u} =>
      Real.exp (c ⬝ᵥ castVec z.val)) (sigma u c) := by
  let : Fintype {r : Fin d → ℤ // castVec r∈halfOpenBox u} :=
    (finite_box_lattice u).fintype
  have hg := hasSum_geometric_product k (fun i=>Real.exp (c ⬝ᵥ castVec (u i)))
    (fun i=>⟨(Real.exp_pos _).le,Real.exp_lt_one_iff.mpr (hc i)⟩)
  have hb := hasSum_fintype (fun r : {r : Fin d → ℤ // castVec r∈halfOpenBox u} =>
      Real.exp (c ⬝ᵥ castVec r.val))
  have hn : ∀ m : Fin k → ℕ, 0≤∏ i,Real.exp (c ⬝ᵥ castVec (u i))^(m i) :=
    fun m=>Finset.prod_nonneg (fun i _=>pow_nonneg (Real.exp_pos _).le (m i))
  have hp := hasSum_mul_nonnegative hb hg (fun r=>(Real.exp_pos _).le) hn
  rw [sigma_eq_box_sum,tsum_fintype]
  rw [← (coneLatticeEquiv u hu).hasSum_iff]
  simpa only [Function.comp_def,exp_coneLatticeEquiv] using hp

end BarvinokCount.ShortFormula.Proof
-- End SigmaSeries

-- Begin SigmaValuation

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma hasSum_sigma_indicator (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (c : Fin d → ℝ) (hc : ∀ i,c ⬝ᵥ castVec (u i)<0) :
    HasSum (fun z : Fin d → ℤ =>
      (cone u).indicator (fun _=>(1:ℝ)) (castVec z)*Real.exp (c ⬝ᵥ castVec z)) (sigma u c) := by
  have hh := hasSum_subtype_iff_indicator (s := {z : Fin d → ℤ | castVec z∈cone u})
    (f := fun z : Fin d → ℤ=>Real.exp (c ⬝ᵥ castVec z)) |>.mp (hasSum_sigma u hu c hc)
  convert hh using 1
  funext z
  by_cases hz : castVec z∈cone u <;> simp [hz]

lemma hasSum_sigmaTermSum (L : List (ConeTerm d))
    (hL : ∀ q∈L,IsSimpleGens q.gens) (c : Fin d → ℝ)
    (hc : ∀ q∈L,∀ i,c ⬝ᵥ castVec (q.gens i)<0) :
    HasSum (fun z : Fin d → ℤ => coneTermSum L (castVec z)*Real.exp (c ⬝ᵥ castVec z))
      (sigmaTermSum L c) := by
  induction L with
  | nil => simp [coneTermSum,sigmaTermSum]
  | cons q L ih =>
    have hq := (hasSum_sigma_indicator q.gens (hL q (by simp)) c (hc q (by simp))).mul_left
      (q.coeff:ℝ)
    have ht := ih (fun r hr=>hL r (by simp [hr])) (fun r hr=>hc r (by simp [hr]))
    simpa only [coneTermSum,sigmaTermSum,List.map_cons,List.sum_cons,ConeTerm.eval,
      ConeTerm.sigmaEval,add_mul,mul_assoc] using hq.add ht

lemma sigma_equality_on_common_negative (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (L : List (ConeTerm d)) (hL : ∀ q∈L,IsSimpleGens q.gens)
    (hid : ∀ x,(cone u).indicator (fun _=>(1:ℝ)) x=coneTermSum L x)
    (c : Fin d → ℝ) (hc : ∀ i,c ⬝ᵥ castVec (u i)<0)
    (hLc : ∀ q∈L,∀ i,c ⬝ᵥ castVec (q.gens i)<0) :
    sigma u c=sigmaTermSum L c := by
  have h := hasSum_sigma_indicator u hu c hc
  simp_rw [hid] at h
  exact h.unique (hasSum_sigmaTermSum L hL c hLc)

end BarvinokCount.ShortFormula.Proof
-- End SigmaValuation

-- Begin BoundaryCard

namespace BarvinokCount.ShortFormula.Proof
variable {I : Type*} [Fintype I] [DecidableEq I]

def nonemptySubsets (s : Finset I) : Finset (Finset I) := s.powerset.filter Finset.Nonempty

omit [Fintype I] in
lemma nonemptySubsets_card (s : Finset I) : (nonemptySubsets s).card=2^s.card-1 := by
  have he : nonemptySubsets s=s.powerset.erase ∅ := by
    ext J
    simp [nonemptySubsets,Finset.nonempty_iff_ne_empty,and_comm]
  rw [he,Finset.card_erase_of_mem (by simp),Finset.card_powerset]

lemma boundary_card_bound (P M : Finset I) (hP : P.Nonempty) (hdis : Disjoint P M) :
    (nonemptySubsets P).card+2*(nonemptySubsets M).card ≤ 2^Fintype.card I := by
  rw [nonemptySubsets_card,nonemptySubsets_card]
  have hp : 2≤2^P.card := by
    have h := Finset.card_pos.mpr hP
    calc
      2=2^1 := by norm_num
      _ ≤ 2^P.card := Nat.pow_le_pow_right (by omega) h
  have hm : 1≤2^M.card := Nat.one_le_pow _ _ (by omega)
  have hn : (2^P.card-1)+2*(2^M.card-1)≤2^P.card*2^M.card := by
    have hp' : 2^P.card-1+1=2^P.card := Nat.sub_add_cancel (by omega)
    have hm' : 2^M.card-1+1=2^M.card := Nat.sub_add_cancel hm
    nlinarith [Nat.zero_le ((2^P.card-2) * (2^M.card-1)),
      Nat.sub_add_cancel hp]
  apply hn.trans
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  rw [← Finset.card_union_of_disjoint hdis]
  exact Finset.card_le_univ _

end BarvinokCount.ShortFormula.Proof
-- End BoundaryCard

-- Begin CoordinateCones

open Set
namespace BarvinokCount.ShortFormula.Proof
variable {I : Type*} [Fintype I] [DecidableEq I]

def coordOrthant : Set (I → ℝ) := {x | ∀ i, 0 ≤ x i}
def coordExtended (a : I → ℝ) : Set (I → ℝ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, t*a i ≤ x i}
def coordFace (a : I → ℝ) (J : Finset I) : Set (I → ℝ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ (∀ i, t*a i ≤ x i) ∧ ∀ i ∈ J, x i = t*a i}
def coordOpenFace (a : I → ℝ) (J : Finset I) : Set (I → ℝ) :=
  {x | ∃ t : ℝ, 0 < t ∧ (∀ i, t*a i ≤ x i) ∧ ∀ i ∈ J, x i = t*a i}
def coordBase (J : Finset I) : Set (I → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i ∈ J, x i = 0}

omit [Fintype I] [DecidableEq I] in
lemma coordOrthant_subset_extended (a : I → ℝ) : coordOrthant ⊆ coordExtended a := by
  intro x hx
  exact ⟨0,le_rfl,by simpa [coordOrthant] using hx⟩

omit [Fintype I] [DecidableEq I] in
lemma coordFace_subset_extended (a : I → ℝ) (J : Finset I) :
    coordFace a J ⊆ coordExtended a := by
  rintro x ⟨t,ht,hx,_⟩
  exact ⟨t,ht,hx⟩

omit [Fintype I] [DecidableEq I] in
lemma coordOpenFace_eq_diff (a : I → ℝ) (J : Finset I)
    (hJ : ∃ j ∈ J, a j ≠ 0) : coordOpenFace a J = coordFace a J \ coordBase J := by
  ext x
  constructor
  · rintro ⟨t,ht,hx,he⟩
    refine ⟨⟨t,ht.le,hx,he⟩,?_⟩
    rintro ⟨_,hz⟩
    obtain ⟨j,hj,haj⟩ := hJ
    have hh := he j hj
    rw [hz j hj] at hh
    exact (mul_ne_zero ht.ne' haj) hh.symm
  · rintro ⟨⟨t,ht,hx,he⟩,hn⟩
    refine ⟨t,lt_of_le_of_ne ht ?_,hx,he⟩
    intro hz
    apply hn
    subst t
    simpa [coordBase] using And.intro hx he

omit [Fintype I] [DecidableEq I] in
lemma coordOpenFace_negative_outside (a : I → ℝ) (J : Finset I)
    (hJ : ∃ j ∈ J, a j < 0) : coordOpenFace a J ⊆ coordExtended a \ coordOrthant := by
  rintro x ⟨t,ht,hx,he⟩
  refine ⟨⟨t,ht.le,hx⟩,?_⟩
  intro ho
  obtain ⟨j,hj,haj⟩ := hJ
  have hh : x j < 0 := by rw [he j hj]; exact mul_neg_of_pos_of_neg ht haj
  exact hh.not_ge (ho j)

end BarvinokCount.ShortFormula.Proof
-- End CoordinateCones

-- Begin CoordinateCover

open Set
namespace BarvinokCount.ShortFormula.Proof
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma positive_cover (a : I → ℝ) (hpos : ∃ j, 0 < a j) :
    coordExtended a = ⋃ j ∈ (Finset.univ.filter fun j => 0 < a j), coordFace a {j} := by
  ext x
  constructor
  · rintro ⟨t,ht,hx⟩
    let P := Finset.univ.filter fun j => 0 < a j
    have hP : P.Nonempty := by
      obtain ⟨j,hj⟩ := hpos
      exact ⟨j,by simpa [P] using hj⟩
    obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image P (fun j => x j / a j) hP
    have haj : 0 < a j := (Finset.mem_filter.mp hj).2
    have htj : t ≤ x j / a j := (le_div_iff₀ haj).2 (hx j)
    refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩
    refine ⟨x j/a j,ht.trans htj,?_,?_⟩
    · intro i
      by_cases hi : 0 < a i
      · exact (le_div_iff₀ hi).1 (hmin i (by simpa [P] using hi))
      · exact (mul_le_mul_of_nonpos_right htj (le_of_not_gt hi)).trans (hx i)
    · intro i hi
      have hij : i=j := Finset.mem_singleton.mp hi
      subst i
      exact (div_mul_cancel₀ _ haj.ne').symm
  · intro hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_,hj⟩ := Set.mem_iUnion.mp hj
    exact coordFace_subset_extended a {j} hj

omit [DecidableEq I] in
lemma negative_cover (a : I → ℝ) :
    coordExtended a \ coordOrthant =
      ⋃ j ∈ (Finset.univ.filter fun j => a j < 0), coordOpenFace a {j} := by
  ext x
  constructor
  · rintro ⟨⟨t,ht,hx⟩,hn⟩
    have hn' : ∃ i, x i < 0 := by
      by_contra hn'
      apply hn
      intro i
      exact le_of_not_gt (fun h => hn' ⟨i,h⟩)
    obtain ⟨i,hxi⟩ := hn'
    have hai : a i < 0 := by
      by_contra h
      have : 0 ≤ t*a i := mul_nonneg ht (le_of_not_gt h)
      linarith [hx i]
    let M := Finset.univ.filter fun j => a j < 0
    have hiM : i∈M := by simpa [M] using hai
    obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image M (fun j => x j / a j) ⟨i,hiM⟩
    have haj : a j < 0 := (Finset.mem_filter.mp hj).2
    have htj : x j/a j ≤ t := (div_le_iff_of_neg haj).2 (hx j)
    have hp : 0 < x j/a j := (div_pos_of_neg_of_neg hxi hai).trans_le (hmax i hiM)
    refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩
    refine ⟨x j/a j,hp,?_,?_⟩
    · intro l
      by_cases hl : a l < 0
      · exact (div_le_iff_of_neg hl).1 (hmax l (by simpa [M] using hl))
      · exact (mul_le_mul_of_nonneg_right htj (le_of_not_gt hl)).trans (hx l)
    · intro l hl
      have hlj : l=j := Finset.mem_singleton.mp hl
      subst l
      exact (div_mul_cancel₀ _ haj.ne).symm
  · intro hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hm,hj⟩ := Set.mem_iUnion.mp hj
    exact coordOpenFace_negative_outside a {j}
      ⟨j,Finset.mem_singleton_self _,(Finset.mem_filter.mp hm).2⟩ hj

end BarvinokCount.ShortFormula.Proof
-- End CoordinateCover

-- Begin CoordinateIntersections

open Set
namespace BarvinokCount.ShortFormula.Proof
variable {I : Type*}

lemma face_parameter_unique (a x : I → ℝ) (i j : I) (t s : ℝ)
    (ht : ∀ l, t*a l ≤ x l) (hs : ∀ l, s*a l ≤ x l)
    (hi : x i=t*a i) (hj : x j=s*a j)
    (ha : (0<a i ∧ 0<a j) ∨ (a i<0 ∧ a j<0)) : t=s := by
  have hi' := hs i
  have hj' := ht j
  rw [hi] at hi'
  rw [hj] at hj'
  rcases ha with ⟨hai,haj⟩ | ⟨hai,haj⟩
  · exact le_antisymm ((mul_le_mul_iff_left₀ haj).mp hj') ((mul_le_mul_iff_left₀ hai).mp hi')
  · exact le_antisymm ((mul_le_mul_right_of_neg hai).mp hi')
      ((mul_le_mul_right_of_neg haj).mp hj')

lemma coordFace_intersection (a : I → ℝ) (J : Finset I) (hJ : J.Nonempty)
    (ha : (∀ i∈J,0<a i) ∨ (∀ i∈J,a i<0)) :
    (⋂ i∈J,coordFace a {i}) = coordFace a J := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := hJ
    obtain ⟨t,ht,hxt,hjt⟩ := Set.mem_iInter.mp (Set.mem_iInter.mp hx j) hj
    refine ⟨t,ht,hxt,?_⟩
    intro i hi
    obtain ⟨s,hs,hxs,his⟩ := Set.mem_iInter.mp (Set.mem_iInter.mp hx i) hi
    have he : t=s := face_parameter_unique a x j i t s hxt hxs
      (hjt j (Finset.mem_singleton_self _)) (his i (Finset.mem_singleton_self _))
      (ha.elim (fun h=>Or.inl ⟨h j hj,h i hi⟩) (fun h=>Or.inr ⟨h j hj,h i hi⟩))
    rw [he]
    exact his i (Finset.mem_singleton_self _)
  · rintro ⟨t,ht,hxt,he⟩
    apply Set.mem_iInter.mpr
    intro i
    apply Set.mem_iInter.mpr
    intro hi
    exact ⟨t,ht,hxt,fun j hj => by simpa only [Finset.mem_singleton.mp hj] using he i hi⟩

lemma coordOpenFace_intersection (a : I → ℝ) (J : Finset I) (hJ : J.Nonempty)
    (ha : (∀ i∈J,0<a i) ∨ (∀ i∈J,a i<0)) :
    (⋂ i∈J,coordOpenFace a {i}) = coordOpenFace a J := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := hJ
    obtain ⟨t,ht,hxt,hjt⟩ := Set.mem_iInter.mp (Set.mem_iInter.mp hx j) hj
    refine ⟨t,ht,hxt,?_⟩
    intro i hi
    obtain ⟨s,hs,hxs,his⟩ := Set.mem_iInter.mp (Set.mem_iInter.mp hx i) hi
    have he : t=s := face_parameter_unique a x j i t s hxt hxs
      (hjt j (Finset.mem_singleton_self _)) (his i (Finset.mem_singleton_self _))
      (ha.elim (fun h=>Or.inl ⟨h j hj,h i hi⟩) (fun h=>Or.inr ⟨h j hj,h i hi⟩))
    rw [he]
    exact his i (Finset.mem_singleton_self _)
  · rintro ⟨t,ht,hxt,he⟩
    apply Set.mem_iInter.mpr
    intro i
    apply Set.mem_iInter.mpr
    intro hi
    exact ⟨t,ht,hxt,fun j hj => by simpa only [Finset.mem_singleton.mp hj] using he i hi⟩

end BarvinokCount.ShortFormula.Proof
-- End CoordinateIntersections

-- Begin CoordinateIdentity

open Set
namespace BarvinokCount.ShortFormula.Proof
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma indicator_diff_one {A B : Set I} (h : B ⊆ A) (x : I) :
    (A \ B).indicator (fun _ => (1:ℝ)) x =
      A.indicator (fun _ => (1:ℝ)) x - B.indicator (fun _ => (1:ℝ)) x := by
  classical
  by_cases hB : x∈B
  · simp [hB,h hB]
  · by_cases hA : x∈A <;> simp [hA,hB]

omit [Fintype I] [DecidableEq I] in
lemma coordBase_subset_face (a : I → ℝ) (J : Finset I) : coordBase J ⊆ coordFace a J := by
  rintro x ⟨hx,hz⟩
  exact ⟨0,le_rfl,by simpa using hx,by simpa using hz⟩

omit [DecidableEq I] in
lemma coordinate_signed_identity (a : I → ℝ) (hpos : ∃ j,0<a j) (x : I → ℝ) :
    coordOrthant.indicator (fun _ => (1:ℝ)) x =
      (∑ J ∈ (Finset.univ.filter (fun j=>0<a j)).powerset.filter Finset.Nonempty,
        ((-1:ℝ)^(J.card+1))*(coordFace a J).indicator (fun _=>1) x) -
      (∑ J ∈ (Finset.univ.filter (fun j=>a j<0)).powerset.filter Finset.Nonempty,
        ((-1:ℝ)^(J.card+1))*((coordFace a J).indicator (fun _=>1) x -
          (coordBase J).indicator (fun _=>1) x)) := by
  classical
  let P := Finset.univ.filter (fun j=>0<a j)
  let M := Finset.univ.filter (fun j=>a j<0)
  have hp := Finset.indicator_biUnion_eq_sum_powerset P (fun j=>coordFace a {j}) (fun _=>(1:ℝ)) x
  have hm := Finset.indicator_biUnion_eq_sum_powerset M (fun j=>coordOpenFace a {j}) (fun _=>(1:ℝ)) x
  rw [← positive_cover a hpos] at hp
  rw [← negative_cover a] at hm
  have hp' : (coordExtended a).indicator (fun _=>(1:ℝ)) x =
      ∑ J ∈ P.powerset.filter Finset.Nonempty,
        ((-1:ℝ)^(J.card+1))*(coordFace a J).indicator (fun _=>1) x := by
    rw [hp]
    apply Finset.sum_congr rfl
    intro J hJ
    obtain ⟨hJP,hJn⟩ := Finset.mem_filter.mp hJ
    have hsub := Finset.mem_powerset.mp hJP
    rw [coordFace_intersection a J hJn (Or.inl (fun j hj => (Finset.mem_filter.mp (hsub hj)).2))]
    simp
  have hm' : (coordExtended a \ coordOrthant).indicator (fun _=>(1:ℝ)) x =
      ∑ J ∈ M.powerset.filter Finset.Nonempty,
        ((-1:ℝ)^(J.card+1))*((coordFace a J).indicator (fun _=>1) x -
          (coordBase J).indicator (fun _=>1) x) := by
    rw [hm]
    apply Finset.sum_congr rfl
    intro J hJ
    obtain ⟨hJM,hJn⟩ := Finset.mem_filter.mp hJ
    have hsub := Finset.mem_powerset.mp hJM
    have ha : ∀ j∈J,a j<0 := fun j hj => (Finset.mem_filter.mp (hsub hj)).2
    rw [coordOpenFace_intersection a J hJn (Or.inr ha)]
    have hn : ∃ j∈J,a j≠0 := by
      obtain ⟨j,hj⟩ := hJn
      exact ⟨j,hj,(ha j hj).ne⟩
    rw [coordOpenFace_eq_diff a J hn,indicator_diff_one (coordBase_subset_face a J)]
    simp
  rw [indicator_diff_one (coordOrthant_subset_extended a)] at hm'
  change _ = _ - _
  rw [← hp',← hm']
  ring

end BarvinokCount.ShortFormula.Proof
-- End CoordinateIdentity

-- Begin IntegralFamily

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof
variable {d : ℕ}

noncomputable def enumGens {I : Type*} [Fintype I] (u : I → Fin d → ℤ) :
    Fin (Fintype.card I) → Fin d → ℤ := fun j => u ((Fintype.equivFin I).symm j)

def familyCone {I : Type*} [Fintype I] (u : I → Fin d → ℤ) : Set (Fin d → ℝ) :=
  {x | ∃ a : I → ℝ, (∀ i,0≤a i) ∧ x=∑ i,a i • castVec (u i)}

lemma enumGens_cone {I : Type*} [Fintype I] (u : I → Fin d → ℤ) :
    cone (enumGens u) = familyCone u := by
  classical
  let e := Fintype.equivFin I
  ext x
  constructor
  · rintro ⟨a,ha,hx⟩
    refine ⟨fun i=>a (e i),fun i=>ha (e i),?_⟩
    rw [hx]
    simpa [enumGens,e] using e.symm.sum_comp (fun i=>a (e i) • castVec (u i))
  · rintro ⟨a,ha,hx⟩
    refine ⟨fun j=>a (e.symm j),fun j=>ha (e.symm j),?_⟩
    rw [hx]
    exact (e.symm.sum_comp (fun i=>a i • castVec (u i))).symm

lemma enumGens_simple {I : Type*} [Fintype I] (u : I → Fin d → ℤ)
    (hu : LinearIndependent ℝ (fun i=>castVec (u i))) : IsSimpleGens (enumGens u) := by
  exact hu.comp _ (Fintype.equivFin I).symm.injective

noncomputable def integerSumMap {I : Type*} [Fintype I] (u : I → Fin d → ℤ) :
    (I → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Fintype.linearCombination ℝ (fun i=>castVec (u i))

lemma integerSumMap_apply {I : Type*} [Fintype I] (u : I → Fin d → ℤ) (a : I → ℝ) :
    integerSumMap u a = ∑ i,a i • castVec (u i) := rfl

lemma integerSumMap_injective {I : Type*} [Fintype I] (u : I → Fin d → ℤ)
    (hu : LinearIndependent ℝ (fun i=>castVec (u i))) :
    Function.Injective (integerSumMap u) := hu.fintypeLinearCombination_injective

end BarvinokCount.ShortFormula.Proof
-- End IntegralFamily

-- Begin FaceCoordinates

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def outsideExtend (J : Finset I) (b : {i : I // i ∉ J} → ℝ) : I → ℝ :=
  fun i => if h : i ∉ J then b ⟨i,h⟩ else 0

omit [Fintype I] in
lemma outsideExtend_nonneg (J : Finset I) (b : {i : I // i ∉ J} → ℝ)
    (hb : ∀ i,0≤b i) : ∀ i,0≤outsideExtend J b i := by
  intro i
  unfold outsideExtend
  split <;> simp_all

omit [Fintype I] in
lemma outsideExtend_zero (J : Finset I) (b : {i : I // i ∉ J} → ℝ)
    {i : I} (hi : i ∈ J) : outsideExtend J b i=0 := by simp [outsideExtend,hi]

lemma outsideExtend_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (J : Finset I) (b : {i : I // i ∉ J} → ℝ) (u : I → E) :
    (∑ i,outsideExtend J b i • u i) = ∑ i : {i : I // i∉J}, b i • u i := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun i=>i∈J)]
  have hz : (∑ i ∈ Finset.univ.filter (fun i=>i∈J),outsideExtend J b i • u i)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [outsideExtend_zero J b (Finset.mem_filter.mp hi).2,zero_smul]
  rw [hz,zero_add]
  rw [← Finset.sum_subtype_eq_sum_filter,Finset.subtype_univ]
  apply Finset.sum_congr rfl
  intro i hi
  simp [outsideExtend,i.property]

omit [Fintype I] in
lemma coordFace_iff_extend (a : I → ℝ) (J : Finset I) (x : I → ℝ) :
    x ∈ coordFace a J ↔ ∃ t : ℝ, 0≤t ∧
      ∃ b : {i : I // i∉J} → ℝ, (∀ i,0≤b i) ∧ x=t • a + outsideExtend J b := by
  constructor
  · rintro ⟨t,ht,hx,he⟩
    refine ⟨t,ht,fun i=>x i-t*a i,fun i=>sub_nonneg.mpr (hx i),?_⟩
    funext i
    by_cases hi : i∈J
    · simp [outsideExtend,hi,he i hi]
    · simp [outsideExtend,hi]
  · rintro ⟨t,ht,b,hb,rfl⟩
    refine ⟨t,ht,?_,?_⟩
    · intro i
      change t*a i ≤ t*a i+outsideExtend J b i
      exact le_add_of_nonneg_right (outsideExtend_nonneg J b hb i)
    · intro i hi
      simp [outsideExtend_zero J b hi]

end BarvinokCount.ShortFormula.Proof
-- End FaceCoordinates

-- Begin FaceFamilies

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof
variable {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def faceFamily (u : I → Fin d → ℤ) (w : Fin d → ℤ) (J : Finset I) :
    Option {i : I // i∉J} → Fin d → ℤ := fun j => j.elim w (fun i=>u i)
def baseFamily (u : I → Fin d → ℤ) (J : Finset I) :
    {i : I // i∉J} → Fin d → ℤ := fun i=>u i

lemma familyCone_faceFamily (u : I → Fin d → ℤ) (w : Fin d → ℤ) (J : Finset I)
    (y : Fin d → ℝ) :
    y ∈ familyCone (faceFamily u w J) ↔
      ∃ t : ℝ, 0≤t ∧ ∃ b : {i : I // i∉J} → ℝ, (∀ i,0≤b i) ∧
        y=t • castVec w+∑ i,b i • castVec (u i) := by
  constructor
  · rintro ⟨b,hb,he⟩
    refine ⟨b none,hb none,fun i=>b (some i),fun i=>hb (some i),?_⟩
    simpa only [Fintype.sum_option,faceFamily,Option.elim_none,Option.elim_some] using he
  · rintro ⟨t,ht,b,hb,he⟩
    refine ⟨fun j=>j.elim t b,?_,?_⟩
    · intro j
      cases j with
      | none => exact ht
      | some i => exact hb i
    · simpa only [Fintype.sum_option,faceFamily,Option.elim_none,Option.elim_some] using he

lemma faceFamily_image (u : I → Fin d → ℤ) (w : Fin d → ℤ) (a : I → ℝ)
    (hw : castVec w=integerSumMap u a) (J : Finset I) :
    familyCone (faceFamily u w J) = (integerSumMap u) '' coordFace a J := by
  ext y
  rw [familyCone_faceFamily]
  constructor
  · rintro ⟨t,ht,b,hb,rfl⟩
    refine ⟨t • a+outsideExtend J b,(coordFace_iff_extend a J _).2 ⟨t,ht,b,hb,rfl⟩,?_⟩
    rw [map_add,map_smul,← hw,integerSumMap_apply,outsideExtend_sum]
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨t,ht,b,hb,rfl⟩ := (coordFace_iff_extend a J x).1 hx
    refine ⟨t,ht,b,hb,?_⟩
    rw [map_add,map_smul,← hw,integerSumMap_apply,outsideExtend_sum]

lemma baseFamily_image (u : I → Fin d → ℤ) (J : Finset I) :
    familyCone (baseFamily u J) = (integerSumMap u) '' coordBase J := by
  ext y
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨outsideExtend J b,⟨outsideExtend_nonneg J b hb,fun i hi=>outsideExtend_zero J b hi⟩,?_⟩
    rw [integerSumMap_apply,outsideExtend_sum]
    rfl
  · rintro ⟨x,⟨hx,hz⟩,rfl⟩
    refine ⟨fun i=>x i,fun i=>hx i,?_⟩
    have he : x=outsideExtend J (fun i=>x i) := by
      funext i
      by_cases hi : i∈J <;> simp [outsideExtend,hi,hz]
    calc
      integerSumMap u x = integerSumMap u (outsideExtend J (fun i=>x i)) := congrArg (integerSumMap u) he
      _ = ∑ i : {i : I // i∉J}, x i • castVec (u i) := outsideExtend_sum J _ _
      _ = _ := rfl

omit [DecidableEq I] in
lemma familyCone_image (u : I → Fin d → ℤ) :
    familyCone u = (integerSumMap u) '' coordOrthant := by
  ext y
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,he.symm⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a,ha,rfl⟩

end BarvinokCount.ShortFormula.Proof
-- End FaceFamilies

-- Begin NativeSignedIdentity

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof

lemma indicator_image_one {A B : Type*} (f : A → B) (hf : Function.Injective f)
    (S : Set A) (x : A) : (f '' S).indicator (fun _ => (1:ℝ)) (f x) = S.indicator (fun _=>1) x := by
  classical
  have h : f x ∈ f '' S ↔ x∈S := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact hf he ▸ hy
    · exact fun hx=>⟨x,hx,rfl⟩
  simp only [Set.indicator_apply,h]

lemma indicator_image_outside {A B : Type*} (f : A → B) (S : Set A) (y : B)
    (hy : y∉Set.range f) : (f '' S).indicator (fun _ => (1:ℝ)) y=0 := by
  classical
  apply Set.indicator_of_notMem
  rintro ⟨x,_,he⟩
  exact hy ⟨x,he⟩

lemma native_signed_identity {d k : ℕ} (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (w : Fin d → ℤ) (a : Fin k → ℝ) (hw : castVec w=integerSumMap u a)
    (hpos : ∃ j,0<a j) (y : Fin d → ℝ) :
    (cone u).indicator (fun _ => (1:ℝ)) y =
      (∑ J ∈ (Finset.univ.filter (fun j=>0<a j)).powerset.filter Finset.Nonempty,
        ((-1:ℝ)^(J.card+1))*(cone (enumGens (faceFamily u w J))).indicator (fun _=>1) y) -
      (∑ J ∈ (Finset.univ.filter (fun j=>a j<0)).powerset.filter Finset.Nonempty,
        ((-1:ℝ)^(J.card+1))*((cone (enumGens (faceFamily u w J))).indicator (fun _=>1) y -
          (cone (enumGens (baseFamily u J))).indicator (fun _=>1) y)) := by
  classical
  have hc : cone u=familyCone u := rfl
  rw [hc,familyCone_image]
  simp_rw [enumGens_cone,faceFamily_image u w a hw,baseFamily_image]
  by_cases hy : y∈Set.range (integerSumMap u)
  · obtain ⟨x,rfl⟩ := hy
    simp_rw [indicator_image_one _ (integerSumMap_injective u hu)]
    exact coordinate_signed_identity a hpos x
  · simp_rw [indicator_image_outside _ _ _ hy]
    simp

end BarvinokCount.ShortFormula.Proof
-- End NativeSignedIdentity

-- Begin FaceEmbedding

namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

noncomputable def faceEmbedding (J : Finset (Fin k)) (j : Fin k) (hj : j∈J) :
    Option {i : Fin k // i∉J} ↪ Fin k where
  toFun q := q.elim j (fun i=>i)
  inj' := by
    intro q r h
    cases q with
    | none =>
      cases r with
      | none => rfl
      | some i =>
        change j=(i:Fin k) at h
        exact False.elim (i.property (h ▸ hj))
    | some i =>
      cases r with
      | none =>
        change (i:Fin k)=j at h
        exact False.elim (i.property (h.symm ▸ hj))
      | some l => exact congrArg some (Subtype.ext h)

lemma faceFamily_eq_update (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (j : Fin k) (hj : j∈J) :
    faceFamily u w J = (Function.update u j w) ∘ faceEmbedding J j hj := by
  funext q
  cases q with
  | none =>
    change w=Function.update u j w j
    simp
  | some i =>
    have hij : (i:Fin k)≠j := fun h=>i.property (h ▸ hj)
    change u i=Function.update u j w i
    simp [Function.update_of_ne hij]

lemma faceFamily_simple (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (j : Fin k) (hj : j∈J)
    (hu : IsSimpleGens (Function.update u j w)) :
    IsSimpleGens (enumGens (faceFamily u w J)) := by
  apply enumGens_simple
  rw [faceFamily_eq_update u w J j hj]
  exact hu.comp _ (faceEmbedding J j hj).injective

lemma baseFamily_simple (u : Fin k → Fin d → ℤ) (J : Finset (Fin k))
    (hu : IsSimpleGens u) : IsSimpleGens (enumGens (baseFamily u J)) := by
  apply enumGens_simple
  exact hu.comp _ Subtype.val_injective

noncomputable def enumFaceEmbedding (J : Finset (Fin k)) (j : Fin k) (hj : j∈J) :
    Fin (Fintype.card (Option {i : Fin k // i∉J})) ↪ Fin k :=
  (Fintype.equivFin (Option {i : Fin k // i∉J})).symm.toEmbedding.trans (faceEmbedding J j hj)

lemma enumFace_eq_update (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (j : Fin k) (hj : j∈J) :
    enumGens (faceFamily u w J) = (Function.update u j w) ∘ enumFaceEmbedding J j hj := by
  rw [faceFamily_eq_update u w J j hj]
  rfl

end BarvinokCount.ShortFormula.Proof
-- End FaceEmbedding

-- Begin FaceIndex

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof

theorem halfOpenBox_comp_subset {d k r : ℕ} (u : Fin k → Fin d → ℤ)
    (e : Fin r ↪ Fin k) : halfOpenBox (u ∘ e) ⊆ halfOpenBox u := by
  classical
  rintro x ⟨a,ha,hx⟩
  let b : Fin k → ℝ := fun j => ∑ i, if e i = j then a i else 0
  have hb (j : Fin k) : 0 ≤ b j ∧ b j < 1 := by
    by_cases hj : ∃ i, e i=j
    · obtain ⟨i,rfl⟩ := hj
      simpa [b,e.injective.eq_iff] using ha i
    · have he (i : Fin r) : e i≠j := fun h => hj ⟨i,h⟩
      simp [b,he]
  refine ⟨b,hb,hx.trans ?_⟩
  symm
  simp only [b,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [ite_smul]

theorem coneIndex_comp_le {d k r : ℕ} (u : Fin k → Fin d → ℤ)
    (e : Fin r ↪ Fin k) : coneIndex (u ∘ e) ≤ coneIndex u := by
  let : Finite {z : Fin d → ℤ // castVec z ∈ halfOpenBox u} := (finite_box_lattice u).to_subtype
  exact Nat.card_le_card_of_injective
    (f := fun z : {z : Fin d → ℤ // castVec z ∈ halfOpenBox (u ∘ e)} =>
      (⟨z.1, halfOpenBox_comp_subset u e z.2⟩ : {z : Fin d → ℤ // castVec z ∈ halfOpenBox u}))
    (by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : {z : Fin d → ℤ // castVec z ∈ halfOpenBox u} => z.1) h)

theorem simple_comp {d k r : ℕ} {u : Fin k → Fin d → ℤ} (hu : IsSimpleGens u)
    (e : Fin r ↪ Fin k) : IsSimpleGens (u ∘ e) := hu.comp e e.injective

end BarvinokCount.ShortFormula.Proof
-- End FaceIndex

-- Begin FaceIndexBounds

namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma faceFamily_index_le (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (j : Fin k) (hj : j∈J) :
    coneIndex (enumGens (faceFamily u w J)) ≤ coneIndex (Function.update u j w) := by
  rw [enumFace_eq_update u w J j hj]
  exact coneIndex_comp_le _ _

noncomputable def enumBaseEmbedding (J : Finset (Fin k)) :
    Fin (Fintype.card {i : Fin k // i∉J}) ↪ Fin k :=
  (Fintype.equivFin {i : Fin k // i∉J}).symm.toEmbedding.trans (Function.Embedding.subtype _)

lemma enumBase_eq_update (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (j : Fin k) (hj : j∈J) :
    enumGens (baseFamily u J) = (Function.update u j w) ∘ enumBaseEmbedding J := by
  funext l
  let i := (Fintype.equivFin {i : Fin k // i∉J}).symm l
  have hij : (i:Fin k)≠j := fun h=>i.property (h ▸ hj)
  change u i=Function.update u j w i
  simp [Function.update_of_ne hij]

lemma baseFamily_index_le (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (j : Fin k) (hj : j∈J) :
    coneIndex (enumGens (baseFamily u J)) ≤ coneIndex (Function.update u j w) := by
  rw [enumBase_eq_update u w J j hj]
  exact coneIndex_comp_le _ _

lemma baseFamily_simple_update (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (j : Fin k) (hj : j∈J)
    (hu : IsSimpleGens (Function.update u j w)) :
    IsSimpleGens (enumGens (baseFamily u J)) := by
  rw [enumBase_eq_update u w J j hj]
  exact simple_comp hu _

end BarvinokCount.ShortFormula.Proof
-- End FaceIndexBounds

-- Begin BoundaryList

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

noncomputable def faceTerm (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (J : Finset (Fin k)) (r : ℤ) : ConeTerm d :=
  ⟨_,enumGens (faceFamily u w J),r⟩
noncomputable def baseTerm (u : Fin k → Fin d → ℤ)
    (J : Finset (Fin k)) (r : ℤ) : ConeTerm d :=
  ⟨_,enumGens (baseFamily u J),r⟩

noncomputable def boundaryList (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (a : Fin k → ℝ) : List (ConeTerm d) :=
  let P := nonemptySubsets (Finset.univ.filter (fun j=>0<a j))
  let M := nonemptySubsets (Finset.univ.filter (fun j=>a j<0))
  P.toList.map (fun J=>faceTerm u w J ((-1)^(J.card+1))) ++
    M.toList.map (fun J=>faceTerm u w J (-((-1)^(J.card+1)))) ++
    M.toList.map (fun J=>baseTerm u J ((-1)^(J.card+1)))

lemma boundaryList_length (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (a : Fin k → ℝ) (hpos : ∃ j,0<a j) : (boundaryList u w a).length ≤ 2^k := by
  have hp : (Finset.univ.filter (fun j=>0<a j)).Nonempty := by
    obtain ⟨j,hj⟩ := hpos
    exact ⟨j,by simp [hj]⟩
  have hd : Disjoint (Finset.univ.filter (fun j=>0<a j))
      (Finset.univ.filter (fun j=>a j<0)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    exact (Finset.mem_filter.mp hj).2.not_gt (Finset.mem_filter.mp hj').2
  have h := boundary_card_bound _ _ hp hd
  simpa [boundaryList,two_mul,add_assoc] using h

lemma boundaryList_identity (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (w : Fin d → ℤ) (a : Fin k → ℝ) (hw : castVec w=integerSumMap u a)
    (hpos : ∃ j,0<a j) (y : Fin d → ℝ) :
    (cone u).indicator (fun _=>(1:ℝ)) y=coneTermSum (boundaryList u w a) y := by
  have h := native_signed_identity u hu w a hw hpos y
  rw [h]
  simp only [boundaryList,coneTermSum,List.map_append,List.sum_append,List.map_map]
  simp only [faceTerm,baseTerm,ConeTerm.eval,Function.comp_def,Int.cast_pow,
    Int.cast_neg,Int.cast_one]
  simp only [Finset.sum_map_toList,nonemptySubsets]
  simp_rw [mul_sub,Finset.sum_sub_distrib,neg_mul,Finset.sum_neg_distrib]
  ring

lemma boundaryList_simple_index (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ)
    (a : Fin k → ℝ) (R : ℝ)
    (hu : ∀ j,a j≠0 → IsSimpleGens (Function.update u j w))
    (hi : ∀ j,a j≠0 → (coneIndex (Function.update u j w):ℝ)≤R) :
    ∀ q∈boundaryList u w a, IsSimpleGens q.gens ∧ (coneIndex q.gens:ℝ)≤R := by
  intro q hq
  simp only [boundaryList,List.mem_append,List.mem_map,Finset.mem_toList] at hq
  have hf (J : Finset (Fin k)) (hj : ∃ j∈J,a j≠0) (r : ℤ) :
      IsSimpleGens (faceTerm u w J r).gens ∧ (coneIndex (faceTerm u w J r).gens:ℝ)≤R := by
    obtain ⟨j,hj,haj⟩ := hj
    have hh : (coneIndex (enumGens (faceFamily u w J)):ℝ) ≤ coneIndex (Function.update u j w) := by
      exact_mod_cast faceFamily_index_le u w J j hj
    exact ⟨faceFamily_simple u w J j hj (hu j haj),hh.trans (hi j haj)⟩
  have hb (J : Finset (Fin k)) (hj : ∃ j∈J,a j≠0) (r : ℤ) :
      IsSimpleGens (baseTerm u J r).gens ∧ (coneIndex (baseTerm u J r).gens:ℝ)≤R := by
    obtain ⟨j,hj,haj⟩ := hj
    have hh : (coneIndex (enumGens (baseFamily u J)):ℝ) ≤ coneIndex (Function.update u j w) := by
      exact_mod_cast baseFamily_index_le u w J j hj
    exact ⟨baseFamily_simple_update u w J j hj (hu j haj),hh.trans (hi j haj)⟩
  have hs (J : Finset (Fin k)) (p : Fin k → Prop) [DecidablePred p]
      (hJ : J∈nonemptySubsets (Finset.univ.filter p)) (hp : ∀ j,p j→a j≠0) :
      ∃ j∈J,a j≠0 := by
    obtain ⟨hsub,hn⟩ := Finset.mem_filter.mp hJ
    obtain ⟨j,hj⟩ := hn
    exact ⟨j,hj,hp j (Finset.mem_filter.mp ((Finset.mem_powerset.mp hsub) hj)).2⟩
  rcases hq with (⟨J,hJ,rfl⟩ | ⟨J,hJ,rfl⟩) | ⟨J,hJ,rfl⟩
  · exact hf J (hs J _ hJ (fun j hj=>ne_of_gt hj)) _
  · exact hf J (hs J _ hJ (fun j hj=>ne_of_lt hj)) _
  · exact hb J (hs J _ hJ (fun j hj=>ne_of_lt hj)) _

end BarvinokCount.ShortFormula.Proof
-- End BoundaryList

-- Begin CommonHalfspace

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma prescribed_dot_products (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (b : Fin k → ℝ) : ∃ c : Fin d → ℝ, ∀ i,c ⬝ᵥ castVec (u i)=b i := by
  classical
  obtain ⟨L,hL⟩ := (integerSumMap u).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (integerSumMap_injective u hu))
  let F : (Fin d → ℝ) →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ b).comp L
  let c : Fin d → ℝ := fun j=>F (Pi.single j 1)
  have hc (x : Fin d → ℝ) : c ⬝ᵥ x=F x := by
    have hx : x=∑ j,x j • Pi.single j (1:ℝ) := pi_eq_sum_univ' x
    conv_rhs => rw [hx]
    simp [c,dotProduct,map_sum,map_smul,mul_comm]
  refine ⟨c,fun i=>?_⟩
  rw [hc]
  have hi : integerSumMap u (Pi.single i 1)=castVec (u i) := by simp [integerSumMap_apply]
  rw [← hi]
  have hLi := DFunLike.congr_fun hL (Pi.single i 1)
  change L (integerSumMap u (Pi.single i 1))=Pi.single i 1 at hLi
  simp [F,hLi]

lemma positive_weights (a : Fin k → ℝ) (hpos : ∃ j,0<a j) :
    ∃ b : Fin k → ℝ, (∀ i,0<b i) ∧ 0<∑ i,b i*a i := by
  classical
  obtain ⟨j,hj⟩ := hpos
  let t := (|∑ i,a i|+1)/a j
  have ht : 0<t := div_pos (by positivity) hj
  let b : Fin k → ℝ := fun i=>1+if i=j then t else 0
  refine ⟨b,fun i=>by dsimp [b]; split_ifs <;> linarith,?_⟩
  have he : ∑ i,b i*a i=(∑ i,a i)+t*a j := by
    simp only [b,add_mul,one_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
    simp
  rw [he]
  dsimp [t]
  rw [div_mul_cancel₀ _ hj.ne']
  have hh := neg_abs_le (∑ i,a i)
  linarith

lemma common_negative_direction (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (w : Fin d → ℤ) (a : Fin k → ℝ) (hw : castVec w=integerSumMap u a)
    (hpos : ∃ j,0<a j) :
    ∃ c : Fin d → ℝ, (∀ i,c ⬝ᵥ castVec (u i)<0) ∧ c ⬝ᵥ castVec w<0 := by
  obtain ⟨b,hb,ha⟩ := positive_weights a hpos
  obtain ⟨c,hc⟩ := prescribed_dot_products u hu (-b)
  refine ⟨c,fun i=>by rw [hc]; exact neg_neg_of_pos (hb i),?_⟩
  rw [hw,integerSumMap_apply,dotProduct_sum]
  simp_rw [dotProduct_smul,hc,Pi.neg_apply,smul_eq_mul,mul_neg,Finset.sum_neg_distrib]
  have hh : (∑ i,a i*b i)=(∑ i,b i*a i) := by apply Finset.sum_congr rfl; intro i _; ring
  rw [hh]
  exact neg_neg_of_pos ha

end BarvinokCount.ShortFormula.Proof
-- End CommonHalfspace

-- Begin BoundaryNegative

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma boundaryList_negative (u : Fin k → Fin d → ℤ) (w : Fin d → ℤ) (a : Fin k → ℝ)
    (c : Fin d → ℝ) (hu : ∀ i,c ⬝ᵥ castVec (u i)<0) (hw : c ⬝ᵥ castVec w<0) :
    ∀ q∈boundaryList u w a,∀ i,c ⬝ᵥ castVec (q.gens i)<0 := by
  intro q hq i
  simp only [boundaryList,List.mem_append,List.mem_map] at hq
  have hf (J : Finset (Fin k)) (r : ℤ) (i : Fin (faceTerm u w J r).dim) :
      c ⬝ᵥ castVec ((faceTerm u w J r).gens i)<0 := by
    change c ⬝ᵥ castVec (faceFamily u w J ((Fintype.equivFin _).symm i))<0
    cases (Fintype.equivFin (Option {i : Fin k // i∉J})).symm i with
    | none => exact hw
    | some j => exact hu j.val
  rcases hq with (⟨J,_,rfl⟩ | ⟨J,_,rfl⟩) | ⟨J,_,rfl⟩
  · exact hf J _ i
  · exact hf J _ i
  · exact hu (((Fintype.equivFin {j : Fin k // j∉J}).symm i).val)

lemma eventually_negative (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ)
    (hc : ∀ i,c ⬝ᵥ castVec (u i)<0) :
    ∀ᶠ x in 𝓝 c,∀ i,x ⬝ᵥ castVec (u i)<0 := by
  apply Filter.eventually_all.mpr
  intro i
  have hcont : Continuous (fun x : Fin d → ℝ => x ⬝ᵥ castVec (u i)) := by
    unfold dotProduct
    fun_prop
  exact hcont.continuousAt.eventually_lt_const (hc i)

end BarvinokCount.ShortFormula.Proof
-- End BoundaryNegative

-- Begin BoundarySigma

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma boundaryList_sigma (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u)
    (w : Fin d → ℤ) (a : Fin k → ℝ) (hw : castVec w=integerSumMap u a)
    (hpos : ∃ j,0<a j)
    (hL : ∀ q∈boundaryList u w a,IsSimpleGens q.gens)
    (c : Fin d → ℝ) (hc : IsRegular u c) (hLc : ListRegular (boundaryList u w a) c) :
    sigma u c=sigmaTermSum (boundaryList u w a) c := by
  obtain ⟨c₀,hc₀,hw₀⟩ := common_negative_direction u hu w a hw hpos
  have hwcont : Continuous (fun x : Fin d → ℝ=>x ⬝ᵥ castVec w) := by
    unfold dotProduct
    fun_prop
  have hen : ∀ᶠ x in 𝓝 c₀,(∀ i,x ⬝ᵥ castVec (u i)<0) ∧ x ⬝ᵥ castVec w<0 :=
    (eventually_negative u c₀ hc₀).and (hwcont.continuousAt.eventually_lt_const hw₀)
  let orig : List (ConeTerm d) := [⟨k,u,1⟩]
  have hreg : ∀ᶠ x in 𝓝 c₀,ListRegular orig x ∧ ListRegular (boundaryList u w a) x := by
    filter_upwards [hen] with x hx
    constructor
    · intro q hq i
      have hq' : q=⟨k,u,1⟩ := by simpa [orig] using hq
      subst q
      exact (hx.1 i).ne
    · intro q hq i
      exact (boundaryList_negative u w a x hx.1 hx.2 q hq i).ne
  have he : ∀ᶠ x in 𝓝 c₀,sigmaTermSum orig x=sigmaTermSum (boundaryList u w a) x := by
    filter_upwards [hen] with x hx
    have hh := sigma_equality_on_common_negative u hu (boundaryList u w a) hL
      (boundaryList_identity u hu w a hw hpos) x hx.1 (boundaryList_negative u w a x hx.1 hx.2)
    simpa [orig,sigmaTermSum,ConeTerm.sigmaEval] using hh
  have horeg : ListRegular orig c := by
    intro q hq
    have hq' : q=⟨k,u,1⟩ := by simpa [orig] using hq
    subst q
    exact hc
  have hh := sigmaTermSum_global_of_local orig (boundaryList u w a) c₀ hreg he c horeg hLc
  simpa [orig,sigmaTermSum,ConeTerm.sigmaEval] using hh

end BarvinokCount.ShortFormula.Proof
-- End BoundarySigma

-- Begin CoordinateLattice

open scoped BigOperators
open Set Submodule
namespace BarvinokCount.ShortFormula.Proof

noncomputable def integerLattice (k : ℕ) : Submodule ℤ (Fin k → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))

instance integerLattice_discrete (k : ℕ) : DiscreteTopology (integerLattice k) :=
  ZSpan.discreteTopology_pi_basisFun

instance integerLattice_full (k : ℕ) : IsZLattice ℝ (integerLattice k) :=
  instIsZLatticeRealSpan _

theorem mem_integerLattice_iff {k : ℕ} (x : Fin k → ℝ) :
    x ∈ integerLattice k ↔ ∃ z : Fin k → ℤ, castVec z=x := by
  rw [integerLattice,(Pi.basisFun ℝ (Fin k)).mem_span_iff_repr_mem ℤ]
  constructor
  · intro hx
    choose z hz using hx
    exact ⟨z,funext hz⟩
  · rintro ⟨z,rfl⟩
    intro i
    exact ⟨z i,rfl⟩

noncomputable def coordinateMap {d k : ℕ} (u : Fin k → Fin d → ℤ) :
    (Fin k → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Fintype.linearCombination ℝ (fun i => castVec (u i))

@[simp] theorem coordinateMap_apply {d k : ℕ} (u : Fin k → Fin d → ℤ) (a : Fin k → ℝ) :
    coordinateMap u a = ∑ i, a i • castVec (u i) := rfl

noncomputable def coordinateLattice {d k : ℕ} (u : Fin k → Fin d → ℤ) :
    Submodule ℤ (Fin k → ℝ) := ZLattice.comap ℝ (integerLattice d) (coordinateMap u)

@[simp] theorem mem_coordinateLattice_iff {d k : ℕ} (u : Fin k → Fin d → ℤ) (a : Fin k → ℝ) :
    a ∈ coordinateLattice u ↔ ∃ z : Fin d → ℤ, castVec z=coordinateMap u a :=
  mem_integerLattice_iff _

theorem coordinateLattice_discrete {d k : ℕ} {u : Fin k → Fin d → ℤ} (hu : IsSimpleGens u) :
    DiscreteTopology (coordinateLattice u) :=
  ZLattice.comap_discreteTopology ℝ (integerLattice d)
    (coordinateMap u).continuous_of_finiteDimensional hu.fintypeLinearCombination_injective

theorem integerLattice_le_coordinateLattice {d k : ℕ} (u : Fin k → Fin d → ℤ) :
    integerLattice k ≤ coordinateLattice u := by
  intro a ha
  obtain ⟨z,rfl⟩ := (mem_integerLattice_iff a).mp ha
  apply (mem_coordinateLattice_iff u _).mpr
  refine ⟨∑ i, z i • u i,?_⟩
  ext j
  simp [castVec]

theorem coordinateLattice_full {d k : ℕ} {u : Fin k → Fin d → ℤ} (hu : IsSimpleGens u) :
    let := coordinateLattice_discrete hu
    IsZLattice ℝ (coordinateLattice u) := by
  let := coordinateLattice_discrete hu
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := integerLattice k)]
  exact Submodule.span_mono (integerLattice_le_coordinateLattice u)

end BarvinokCount.ShortFormula.Proof
-- End CoordinateLattice

-- Begin LatticeQuotient

open scoped BigOperators
open Set Submodule
namespace BarvinokCount.ShortFormula.Proof

noncomputable def latticeFract {k : ℕ} (L : Submodule ℤ (Fin k → ℝ))
    (hL : integerLattice k ≤ L) (x : L) : L :=
  ⟨ZSpan.fract (Pi.basisFun ℝ (Fin k)) x,
    L.sub_mem x.2 (hL (ZSpan.floor (Pi.basisFun ℝ (Fin k)) x).2)⟩

noncomputable def latticeBoxQuotientEquiv {k : ℕ} (L : Submodule ℤ (Fin k → ℝ))
    (hL : integerLattice k ≤ L) :
    (L ⧸ (integerLattice k).comap L.subtype) ≃
      {x : L // (x : Fin k → ℝ) ∈ ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k))} := by
  let F : L → {x : L // (x : Fin k → ℝ) ∈ ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k))} :=
    fun x => ⟨latticeFract L hL x,ZSpan.fract_mem_fundamentalDomain _ _⟩
  have he (x y : L) : F x=F y ↔ -x+y ∈ (integerLattice k).comap L.subtype := by
    constructor
    · intro h
      have hh : ZSpan.fract (Pi.basisFun ℝ (Fin k)) (x : Fin k → ℝ) =
          ZSpan.fract (Pi.basisFun ℝ (Fin k)) (y : Fin k → ℝ) :=
        congrArg (fun z => ((z.1 : L) : Fin k → ℝ)) h
      exact (ZSpan.fract_eq_fract _ _ _).mp hh
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      exact (ZSpan.fract_eq_fract _ _ _).mpr h
  refine Equiv.ofBijective (Quotient.lift F (fun x y h => (he x y).mpr ?_)) ?_
  · exact QuotientAddGroup.leftRel_apply.mp h
  · constructor
    · intro x y
      induction x,y using Quotient.inductionOn₂
      intro h
      apply Quotient.sound'
      exact QuotientAddGroup.leftRel_apply.mpr ((he _ _).mp h)
    · intro x
      refine ⟨Submodule.Quotient.mk x.1,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact ZSpan.fract_eq_self.mpr x.2

end BarvinokCount.ShortFormula.Proof
-- End LatticeQuotient

-- Begin BoxQuotient

open scoped BigOperators
open Set Submodule
namespace BarvinokCount.ShortFormula.Proof

noncomputable def coordinateBoxEquiv {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) :
    {a : coordinateLattice u // (a : Fin k → ℝ) ∈ ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k))} ≃
      {z : Fin d → ℤ // castVec z ∈ halfOpenBox u} := by
  let F : {a : coordinateLattice u // (a : Fin k → ℝ) ∈ ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k))} →
      {z : Fin d → ℤ // castVec z ∈ halfOpenBox u} := fun a =>
    ⟨((mem_coordinateLattice_iff u a.1).mp a.1.2).choose,
      ⟨a.1,fun i => a.2 i,((mem_coordinateLattice_iff u a.1).mp a.1.2).choose_spec⟩⟩
  refine Equiv.ofBijective F ⟨?_,?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply hu.fintypeLinearCombination_injective
    have ha := ((mem_coordinateLattice_iff u a.1).mp a.1.2).choose_spec
    have hb := ((mem_coordinateLattice_iff u b.1).mp b.1.2).choose_spec
    exact ha.symm.trans ((congrArg (fun z => castVec z.1) hab).trans hb)
  · rintro ⟨z,a,ha,hz⟩
    have hm : a ∈ coordinateLattice u := (mem_coordinateLattice_iff u a).mpr ⟨z,hz⟩
    refine ⟨⟨⟨a,hm⟩,ha⟩,?_⟩
    apply Subtype.ext
    apply castVec_injective
    exact ((mem_coordinateLattice_iff u a).mp hm).choose_spec.trans hz.symm

theorem index_eq_relIndex {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) :
    coneIndex u = (integerLattice k).toAddSubgroup.relIndex (coordinateLattice u).toAddSubgroup := by
  let e := (latticeBoxQuotientEquiv (coordinateLattice u) (integerLattice_le_coordinateLattice u)).trans
    (coordinateBoxEquiv u hu)
  exact (Nat.card_congr e).symm

theorem integerLattice_covolume (k : ℕ) : ZLattice.covolume (integerLattice k) = 1 := by
  rw [ZLattice.covolume_eq_det (integerLattice k) ((Pi.basisFun ℝ (Fin k)).restrictScalars ℤ)]
  trans |(1 : Matrix (Fin k) (Fin k) ℝ).det|
  · congr 2
    ext i j
    have h := (Pi.basisFun ℝ (Fin k)).restrictScalars_apply ℤ i
    have hh := congrFun h j
    exact hh.trans (by simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm])
  · simp

theorem coordinateLattice_covolume {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) :
    letI := coordinateLattice_discrete hu
    letI := coordinateLattice_full hu
    ZLattice.covolume (coordinateLattice u) = (coneIndex u : ℝ)⁻¹ := by
  let := coordinateLattice_discrete hu
  let := coordinateLattice_full hu
  have h := ZLattice.covolume_div_covolume_eq_relIndex (integerLattice k)
    (coordinateLattice u) (integerLattice_le_coordinateLattice u)
  rw [integerLattice_covolume,one_div,← index_eq_relIndex u hu] at h
  simpa using congrArg (fun x : ℝ => x⁻¹) h

end BarvinokCount.ShortFormula.Proof
-- End BoxQuotient

-- Begin LatticeCube

open scoped BigOperators ENNReal
open Set MeasureTheory
namespace BarvinokCount.ShortFormula.Proof

theorem lattice_cube_point {k : ℕ} (hk : 0 < k) (L : Submodule ℤ (Fin k → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (r : ℝ) (hr : 0 ≤ r)
    (hv : ZLattice.covolume L ≤ r ^ k) :
    ∃ a : L, a ≠ 0 ∧ ∀ i, |(a : Fin k → ℝ) i| ≤ r := by
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  let : Countable L.toAddSubgroup := countable_of_Lindelof_of_discrete
  let b := IsZLattice.basis L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hF := ZLattice.isAddFundamentalDomain b volume
  have hfinite : volume F ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top.ne
  have hvol : volume F = ENNReal.ofReal (ZLattice.covolume L) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
    exact (ENNReal.ofReal_toReal hfinite).symm
  have hc : volume (Icc (fun _ : Fin k => -r) (fun _ => r)) =
      ENNReal.ofReal ((2*r)^k) := by
    rw [Real.volume_Icc_pi]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [ENNReal.ofReal_pow (by positivity)]
  have hmeasure : volume F * 2 ^ Module.finrank ℝ (Fin k → ℝ) ≤
      volume (Icc (fun _ : Fin k => -r) (fun _ => r)) := by
    rw [hvol,hc,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
    have he : (2 : ℝ≥0∞)^k = ENNReal.ofReal ((2 : ℝ)^k) := by simp
    rw [he, ← ENNReal.ofReal_mul (le_of_lt (ZLattice.covolume_pos L volume))]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_pow]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k]
  obtain ⟨a,ha,hbox⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (L := L.toAddSubgroup) (s := Icc (fun _ : Fin k => -r) (fun _ => r)) hF
      (fun x hx => ⟨fun i => by simpa using neg_le_neg (hx.2 i),
        fun i => by simpa using neg_le_neg (hx.1 i)⟩)
      (convex_Icc _ _) isCompact_Icc hmeasure
  exact ⟨a,ha,fun i => abs_le.mpr ⟨hbox.1 i,hbox.2 i⟩⟩

end BarvinokCount.ShortFormula.Proof
-- End LatticeCube

-- Begin BasisBoxQuotient

open scoped BigOperators
open Set Submodule
namespace BarvinokCount.ShortFormula.Proof

noncomputable def basisLatticeFract {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ)) (L : Submodule ℤ (Fin k → ℝ))
    (hL : Submodule.span ℤ (Set.range b) ≤ L) (x : L) : L :=
  ⟨ZSpan.fract b x,
    L.sub_mem x.2 (hL (ZSpan.floor b x).2)⟩

noncomputable def basisLatticeBoxQuotientEquiv {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ)) (L : Submodule ℤ (Fin k → ℝ))
    (hL : Submodule.span ℤ (Set.range b) ≤ L) :
    (L ⧸ (Submodule.span ℤ (Set.range b)).comap L.subtype) ≃
      {x : L // (x : Fin k → ℝ) ∈ ZSpan.fundamentalDomain b} := by
  let F : L → {x : L // (x : Fin k → ℝ) ∈ ZSpan.fundamentalDomain b} :=
    fun x => ⟨basisLatticeFract b L hL x,ZSpan.fract_mem_fundamentalDomain _ _⟩
  have he (x y : L) : F x=F y ↔ -x+y ∈ (Submodule.span ℤ (Set.range b)).comap L.subtype := by
    constructor
    · intro h
      have hh : ZSpan.fract b (x : Fin k → ℝ) =
          ZSpan.fract b (y : Fin k → ℝ) :=
        congrArg (fun z => ((z.1 : L) : Fin k → ℝ)) h
      exact (ZSpan.fract_eq_fract _ _ _).mp hh
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      exact (ZSpan.fract_eq_fract _ _ _).mpr h
  refine Equiv.ofBijective (Quotient.lift F (fun x y h => (he x y).mpr ?_)) ?_
  · exact QuotientAddGroup.leftRel_apply.mp h
  · constructor
    · intro x y
      induction x,y using Quotient.inductionOn₂
      intro h
      apply Quotient.sound'
      exact QuotientAddGroup.leftRel_apply.mpr ((he _ _).mp h)
    · intro x
      refine ⟨Submodule.Quotient.mk x.1,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact ZSpan.fract_eq_self.mpr x.2

end BarvinokCount.ShortFormula.Proof
-- End BasisBoxQuotient

-- Begin BasisIndex

open scoped BigOperators
open Set Submodule
namespace BarvinokCount.ShortFormula.Proof

noncomputable def basisCoordinateBoxEquiv {d k : ℕ} (u w : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (hw : ∀ i, castVec (w i) = coordinateMap u (b i)) :
    {a : coordinateLattice u // (a : Fin k → ℝ) ∈ ZSpan.fundamentalDomain b} ≃
      {z : Fin d → ℤ // castVec z ∈ halfOpenBox w} := by
  have hsum (a : Fin k → ℝ) : coordinateMap u a =
      ∑ i, b.repr a i • castVec (w i) := by
    simp_rw [hw]
    calc
      coordinateMap u a = coordinateMap u (∑ i, b.repr a i • b i) :=
        congrArg (coordinateMap u) (b.sum_repr a).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact map_smul (coordinateMap u) _ _
  let F : {a : coordinateLattice u // (a : Fin k → ℝ) ∈ ZSpan.fundamentalDomain b} →
      {z : Fin d → ℤ // castVec z ∈ halfOpenBox w} := fun a =>
    ⟨((mem_coordinateLattice_iff u a.1).mp a.1.2).choose,
      ⟨fun i => b.repr a.1 i, a.2,
        ((mem_coordinateLattice_iff u a.1).mp a.1.2).choose_spec.trans (hsum a.1)⟩⟩
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro a a' h
    apply Subtype.ext
    apply Subtype.ext
    apply hu.fintypeLinearCombination_injective
    exact (((mem_coordinateLattice_iff u a.1).mp a.1.2).choose_spec).symm.trans
      ((congrArg (fun z => castVec z.1) h).trans
        ((mem_coordinateLattice_iff u a'.1).mp a'.1.2).choose_spec)
  · rintro ⟨z, c, hc, hz⟩
    let a := ∑ i, c i • b i
    have ha : castVec z = coordinateMap u a := by
      rw [hz]
      simp [a, hw]
    have hm : a ∈ coordinateLattice u := (mem_coordinateLattice_iff u a).mpr ⟨z,ha⟩
    have hbox : a ∈ ZSpan.fundamentalDomain b := by
      intro i
      simpa [a, Finsupp.sum_apply, Finsupp.single_apply] using hc i
    refine ⟨⟨⟨a,hm⟩,hbox⟩, ?_⟩
    apply Subtype.ext
    apply castVec_injective
    exact ((mem_coordinateLattice_iff u a).mp hm).choose_spec.trans ha.symm

theorem basis_span_le_coordinateLattice {d k : ℕ} (u w : Fin k → Fin d → ℤ)
    (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (hw : ∀ i, castVec (w i) = coordinateMap u (b i)) :
    Submodule.span ℤ (Set.range b) ≤ coordinateLattice u := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact (mem_coordinateLattice_iff u _).mpr ⟨w i,hw i⟩

theorem basis_index_eq_relIndex {d k : ℕ} (u w : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (hw : ∀ i, castVec (w i) = coordinateMap u (b i)) :
    coneIndex w = (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex
      (coordinateLattice u).toAddSubgroup := by
  exact (Nat.card_congr ((basisLatticeBoxQuotientEquiv b (coordinateLattice u)
    (basis_span_le_coordinateLattice u w b hw)).trans
    (basisCoordinateBoxEquiv u w hu b hw))).symm

theorem basis_covolume {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ)) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |(Matrix.of b).det| := by
  rw [ZLattice.covolume_eq_det _ (b.restrictScalars ℤ)]
  congr 2
  ext i j
  exact congrFun (b.restrictScalars_apply ℤ i) j

theorem basis_index_formula {d k : ℕ} (u w : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (hw : ∀ i, castVec (w i) = coordinateMap u (b i)) :
    (coneIndex w : ℝ) = |(Matrix.of b).det| * coneIndex u := by
  let := coordinateLattice_discrete hu
  let := coordinateLattice_full hu
  have h := ZLattice.covolume_div_covolume_eq_relIndex
    (Submodule.span ℤ (Set.range b)) (coordinateLattice u)
    (basis_span_le_coordinateLattice u w b hw)
  rw [basis_covolume, coordinateLattice_covolume u hu,
    ← basis_index_eq_relIndex u w hu b hw, div_inv_eq_mul] at h
  exact h.symm

end BarvinokCount.ShortFormula.Proof
-- End BasisIndex

-- Begin ReplacementMatrix

open scoped BigOperators Matrix
namespace BarvinokCount.ShortFormula.Proof

noncomputable def replacementMatrix {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    Matrix (Fin k) (Fin k) ℝ := (1 : Matrix (Fin k) (Fin k) ℝ).updateRow j a

theorem replacementMatrix_det {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    (replacementMatrix a j).det = a j := by
  have h := Matrix.det_updateRow_sum (1 : Matrix (Fin k) (Fin k) ℝ) j a
  have he : (∑ i, a i • (1 : Matrix (Fin k) (Fin k) ℝ) i) = a := by
    ext l
    simp [Finset.sum_apply, Pi.smul_apply, Matrix.one_apply]
  rw [he] at h
  simpa [replacementMatrix] using h

theorem replacementMatrix_li {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    LinearIndependent ℝ (replacementMatrix a j).row ↔ a j ≠ 0 := by
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    replacementMatrix_det, isUnit_iff_ne_zero]

noncomputable def replacementBasis {k : ℕ} (a : Fin k → ℝ) (j : Fin k) (hj : a j ≠ 0) :
    Module.Basis (Fin k) ℝ (Fin k → ℝ) :=
  (Pi.basisFun ℝ (Fin k)).map ((replacementMatrix a j).transpose.toLinearEquiv
    (Pi.basisFun ℝ (Fin k)) (by
      rw [Matrix.det_transpose, replacementMatrix_det]
      exact isUnit_iff_ne_zero.mpr hj))

theorem replacementBasis_apply {k : ℕ} (a : Fin k → ℝ) (j : Fin k) (hj : a j ≠ 0)
    (i : Fin k) : replacementBasis a j hj i = (replacementMatrix a j).row i := by
  simp [replacementBasis, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply, Matrix.row, Matrix.col]

theorem replacementBasis_det {k : ℕ} (a : Fin k → ℝ) (j : Fin k) (hj : a j ≠ 0) :
    (Matrix.of (replacementBasis a j hj)).det = a j := by
  have he : Matrix.of (replacementBasis a j hj) = replacementMatrix a j := by
    ext i l
    exact congrFun (replacementBasis_apply a j hj i) l
  rw [he, replacementMatrix_det]

end BarvinokCount.ShortFormula.Proof
-- End ReplacementMatrix

-- Begin ReplacementIndex

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

theorem replacement_coordinate {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (w : Fin d → ℤ) (a : Fin k → ℝ) (hw : castVec w = coordinateMap u a)
    (j i : Fin k) :
    castVec (Function.update u j w i) = coordinateMap u ((replacementMatrix a j).row i) := by
  change castVec (Function.update u j w i) =
    coordinateMap u ((1 : Matrix (Fin k) (Fin k) ℝ).updateRow j a i)
  by_cases h : i = j
  · subst i
    rw [Function.update_self, Matrix.updateRow_self]
    exact hw
  · rw [Function.update_of_ne h, Matrix.updateRow_ne h]
    simp [Matrix.one_apply, coordinateMap, Fintype.linearCombination_apply]

theorem replacement_simple_iff {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) (w : Fin d → ℤ) (a : Fin k → ℝ)
    (hw : castVec w = coordinateMap u a) (j : Fin k) :
    IsSimpleGens (Function.update u j w) ↔ a j ≠ 0 := by
  have he : (fun i => castVec (Function.update u j w i)) =
      (coordinateMap u) ∘ (replacementMatrix a j).row :=
    funext (replacement_coordinate u w a hw j)
  change LinearIndependent ℝ (fun i => castVec (Function.update u j w i)) ↔ _
  rw [he]
  constructor
  · intro h
    exact (replacementMatrix_li a j).mp (h.of_comp (coordinateMap u))
  · intro h
    exact ((replacementMatrix_li a j).mpr h).map'
      (coordinateMap u) (LinearMap.ker_eq_bot.mpr hu.fintypeLinearCombination_injective)

theorem replacement_index {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) (w : Fin d → ℤ) (a : Fin k → ℝ)
    (hw : castVec w = coordinateMap u a) (j : Fin k) (hj : a j ≠ 0) :
    (coneIndex (Function.update u j w) : ℝ) = |a j| * coneIndex u := by
  have h := basis_index_formula u (Function.update u j w) hu (replacementBasis a j hj)
    (fun i => (replacement_coordinate u w a hw j i).trans
      (congrArg (coordinateMap u) (replacementBasis_apply a j hj i).symm))
  simpa [replacementBasis_det] using h

end BarvinokCount.ShortFormula.Proof
-- End ReplacementIndex

-- Begin SmallLatticeVector

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

noncomputable def indexRadius (k N : ℕ) : ℝ := ((N : ℝ)⁻¹) ^ (k : ℝ)⁻¹

theorem indexRadius_nonneg (k N : ℕ) : 0 ≤ indexRadius k N := by
  exact Real.rpow_nonneg (by positivity) _

theorem indexRadius_pow {k : ℕ} (hk : 0 < k) (N : ℕ) :
    indexRadius k N ^ k = (N : ℝ)⁻¹ :=
  Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hk)

theorem small_lattice_vector {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) (hk : 0 < k) :
    ∃ (w : Fin d → ℤ) (a : Fin k → ℝ), w ≠ 0 ∧
      castVec w = coordinateMap u a ∧ (∃ j, 0 < a j) ∧
      ∀ i, |a i| ≤ indexRadius k (coneIndex u) := by
  let := coordinateLattice_discrete hu
  let := coordinateLattice_full hu
  obtain ⟨a,ha,hbound⟩ := lattice_cube_point hk (coordinateLattice u)
    (indexRadius k (coneIndex u)) (indexRadius_nonneg _ _) (by
      rw [coordinateLattice_covolume u hu,indexRadius_pow hk])
  have han : (a : Fin k → ℝ) ≠ 0 := fun h => ha (Subtype.ext h)
  obtain ⟨i,hi⟩ : ∃ i, (a : Fin k → ℝ) i ≠ 0 := by
    by_contra h
    push Not at h
    exact han (funext h)
  have build (v : coordinateLattice u) (hv : (v : Fin k → ℝ) ≠ 0)
      (hp : ∃ j, 0 < (v : Fin k → ℝ) j)
      (hb : ∀ j, |(v : Fin k → ℝ) j| ≤ indexRadius k (coneIndex u)) :
      ∃ (w : Fin d → ℤ) (a : Fin k → ℝ), w ≠ 0 ∧
        castVec w = coordinateMap u a ∧ (∃ j, 0 < a j) ∧
        ∀ j, |a j| ≤ indexRadius k (coneIndex u) := by
    obtain ⟨w,hw⟩ := (mem_coordinateLattice_iff u v).mp v.2
    refine ⟨w,v,?_,hw,hp,hb⟩
    intro hw0
    have hz : coordinateMap u (v : Fin k → ℝ) = coordinateMap u 0 := by
      rw [← hw, hw0, castVec_zero, map_zero]
    exact hv (hu.fintypeLinearCombination_injective hz)
  rcases lt_or_gt_of_ne hi with hi | hi
  · apply build (-a) (neg_ne_zero.mpr han) ⟨i,neg_pos.mpr hi⟩
    intro j
    simpa using hbound j
  · exact build a han ⟨i,hi⟩ hbound

end BarvinokCount.ShortFormula.Proof
-- End SmallLatticeVector

-- Begin ReducingVector

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

theorem indexRadius_mul {k N : ℕ} (hN : 0 < N) :
    indexRadius k N * N = (N : ℝ) ^ (1 - (k : ℝ)⁻¹) := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  rw [indexRadius, ← Real.rpow_neg_eq_inv_rpow, sub_eq_add_neg,
    Real.rpow_add h, Real.rpow_one, mul_comm]

theorem radius_index_bound {d k N : ℕ} (hk : 0 < k) (hkd : k ≤ d) (hN : 0 < N) :
    indexRadius k N * N ≤ (N : ℝ) ^ (((d : ℝ)-1)/d) := by
  rw [indexRadius_mul hN]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkd' : (k : ℝ) ≤ d := by exact_mod_cast hkd
  have hd' : (0 : ℝ) < d := lt_of_lt_of_le hk' hkd'
  have hi : (d : ℝ)⁻¹ ≤ (k : ℝ)⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le hk' hkd'
  have he : ((d : ℝ)-1)/d = 1-(d : ℝ)⁻¹ := by field_simp
  rw [he]
  linarith

theorem reducing_vector {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) (hk : 0 < k) :
    ∃ (w : Fin d → ℤ) (a : Fin k → ℝ), w ≠ 0 ∧
      castVec w = coordinateMap u a ∧ (∃ j, 0 < a j) ∧
      (∀ j, IsSimpleGens (Function.update u j w) ↔ a j ≠ 0) ∧
      (∀ j, a j ≠ 0 → (coneIndex (Function.update u j w) : ℝ) ≤
        (coneIndex u : ℝ) ^ (((d : ℝ)-1)/d)) := by
  obtain ⟨w,a,hw0,hw,hp,hb⟩ := small_lattice_vector u hu hk
  refine ⟨w,a,hw0,hw,hp,fun j => replacement_simple_iff u hu w a hw j,?_⟩
  intro j hj
  rw [replacement_index u hu w a hw j hj]
  apply le_trans (mul_le_mul_of_nonneg_right (hb j) (by positivity))
  apply radius_index_bound hk _ (coneIndex_pos u)
  have h := hu.fintype_card_le_finrank
  simpa using h

end BarvinokCount.ShortFormula.Proof
-- End ReducingVector

-- Begin PrimitiveIndex

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof

theorem primitive_iff_box_zero {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) : IsPrimitiveGens u ↔
      ∀ z : Fin d → ℤ, castVec z ∈ halfOpenBox u → z=0 := by
  constructor
  · intro hp z hz
    obtain ⟨a,ha,he⟩ := hz
    obtain ⟨m,hm⟩ := hp.2 z (halfOpenBox_subset_span u ⟨a,ha,he⟩)
    have hc : a = fun i => (m i : ℝ) := by
      apply simple_sum_injective hu
      rw [← he,hm]
      ext j
      simp [castVec]
    have hm0 (i : Fin k) : m i=0 := by
      have h := ha i
      rw [congrFun hc i] at h
      have h0 : 0 ≤ m i := by exact_mod_cast h.1
      have h1 : m i < 1 := by exact_mod_cast h.2
      omega
    simpa [hm0] using hm
  · intro h
    refine ⟨hu,?_⟩
    intro z hz
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hz
    let m : Fin k → ℤ := fun i => ⌊a i⌋
    let w : Fin d → ℤ := z - ∑ i, m i • u i
    have hw : castVec w ∈ halfOpenBox u := by
      refine ⟨fun i => Int.fract (a i),fun i => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,?_⟩
      simp only [w,castVec_sub,castVec_sum,castVec_zsmul]
      rw [← ha]
      simp only [Int.fract,sub_smul,Finset.sum_sub_distrib,m]
    have hw0 := h w hw
    refine ⟨m,?_⟩
    exact sub_eq_zero.mp hw0

theorem primitive_iff_index_one {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) : IsPrimitiveGens u ↔ coneIndex u=1 := by
  rw [primitive_iff_box_zero u hu]
  let Z := {z : Fin d → ℤ // castVec z ∈ halfOpenBox u}
  let z0 : Z := ⟨0,by simpa using zero_mem_halfOpenBox u⟩
  change (∀ z : Fin d → ℤ, castVec z ∈ halfOpenBox u → z=0) ↔ Nat.card Z=1
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · intro h
    refine ⟨⟨fun x y => ?_⟩,⟨z0⟩⟩
    exact Subtype.ext ((h x.1 x.2).trans (h y.1 y.2).symm)
  · rintro ⟨hs,hn⟩ w hw
    exact congrArg Subtype.val (hs.elim (⟨w,hw⟩ : Z) z0)

end BarvinokCount.ShortFormula.Proof
-- End PrimitiveIndex

-- Begin ConeStep

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma coneIndex_dim_zero (u : Fin 0 → Fin d → ℤ) (hu : IsSimpleGens u) : coneIndex u=1 := by
  apply (primitive_iff_index_one u hu).mp
  apply (primitive_iff_box_zero u hu).mpr
  intro z hz
  obtain ⟨a,_,he⟩ := hz
  apply castVec_injective
  simpa using he

lemma exists_cone_step (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    ∃ L : List (ConeTerm d),
      L.length≤2^d ∧ (∀ q∈L,IsSimpleGens q.gens) ∧
      (∀ q∈L,(coneIndex q.gens:ℝ)≤(coneIndex u:ℝ)^(((d:ℝ)-1)/d)) ∧
      (∀ x,(cone u).indicator (fun _=>(1:ℝ)) x=coneTermSum L x) ∧
      (∀ c,IsRegular u c→ListRegular L c→sigma u c=sigmaTermSum L c) := by
  classical
  by_cases hk : k=0
  · subst k
    refine ⟨[⟨0,u,1⟩],?_,?_,?_,?_,?_⟩
    · simp only [List.length_singleton]
      exact Nat.one_le_pow _ _ (by norm_num)
    · intro q hq
      have he : q=⟨0,u,1⟩ := by simpa using hq
      subst q
      exact hu
    · intro q hq
      have he : q=⟨0,u,1⟩ := by simpa using hq
      subst q
      simp [coneIndex_dim_zero u hu]
    · intro x
      simp [coneTermSum,ConeTerm.eval]
    · intro c _ _
      simp [sigmaTermSum,ConeTerm.sigmaEval]
  · obtain ⟨w,a,_,hw,hpos,hs,hi⟩ := reducing_vector u hu (Nat.pos_of_ne_zero hk)
    have hw' : castVec w=integerSumMap u a := hw
    have hL := boundaryList_simple_index u w a _ (fun j hj=>(hs j).mpr hj) hi
    refine ⟨boundaryList u w a,?_,fun q hq=>(hL q hq).1,fun q hq=>(hL q hq).2,
      boundaryList_identity u hu w a hw' hpos,?_⟩
    · apply (boundaryList_length u w a hpos).trans
      apply Nat.pow_le_pow_right (by norm_num)
      have hh := hu.fintype_card_le_finrank
      simpa using hh
    · exact boundaryList_sigma u hu w a hw' hpos (fun q hq=>(hL q hq).1)

end BarvinokCount.ShortFormula.Proof
-- End ConeStep

-- Begin RegularDense

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma isOpen_dot_ne_zero (z : Fin d → ℝ) : IsOpen {c : Fin d → ℝ | c ⬝ᵥ z≠0} := by
  have hc : Continuous (fun c : Fin d → ℝ=>c ⬝ᵥ z) := by unfold dotProduct; fun_prop
  exact isOpen_ne.preimage hc

lemma dense_dot_ne_zero (z : Fin d → ℝ) (hz : z≠0) : Dense {c : Fin d → ℝ | c ⬝ᵥ z≠0} := by
  let L : (Fin d → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ z
  have hn : LinearMap.ker L≠⊤ := by
    intro he
    have hm : z∈LinearMap.ker L := he ▸ Submodule.mem_top
    have hzero : z ⬝ᵥ z=0 := hm
    exact hz (dotProduct_self_eq_zero.mp hzero)
  have hint : interior ((LinearMap.ker L : Submodule ℝ (Fin d → ℝ)) : Set (Fin d → ℝ))=∅ := by
    by_contra he
    exact hn ((LinearMap.ker L).eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr he))
  have hh := interior_eq_empty_iff_dense_compl.mp hint
  convert hh using 1
  ext c
  change (c ⬝ᵥ z≠0) ↔ ¬L c=0
  rw [show L c=z ⬝ᵥ c from rfl,dotProduct_comm]

lemma isOpen_regular (u : Fin k → Fin d → ℤ) : IsOpen {c | IsRegular u c} := by
  have he : {c | IsRegular u c}=⋂ i,{c : Fin d → ℝ | c ⬝ᵥ castVec (u i)≠0} := by
    ext c; simp [IsRegular]
  rw [he]
  exact isOpen_iInter_of_finite (fun i=>isOpen_dot_ne_zero _)

lemma dense_regular (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) : Dense {c | IsRegular u c} := by
  have he : {c | IsRegular u c}=⋂ i,{c : Fin d → ℝ | c ⬝ᵥ castVec (u i)≠0} := by
    ext c; simp [IsRegular]
  rw [he]
  exact dense_iInter_of_isOpen (fun i=>isOpen_dot_ne_zero _) (fun i=>dense_dot_ne_zero _ (hu.ne_zero i))

lemma isOpen_listRegular (L : List (ConeTerm d)) : IsOpen {c | ListRegular L c} := by
  induction L with
  | nil => simp [ListRegular]
  | cons q L ih =>
    have he : {c | ListRegular (q::L) c}={c | IsRegular q.gens c}∩{c | ListRegular L c} := by
      ext c; simp [ListRegular]
    rw [he]
    exact (isOpen_regular q.gens).inter ih

lemma dense_listRegular (L : List (ConeTerm d)) (hL : ∀ q∈L,IsSimpleGens q.gens) :
    Dense {c | ListRegular L c} := by
  induction L with
  | nil => simp [ListRegular]
  | cons q L ih =>
    have he : {c | ListRegular (q::L) c}={c | IsRegular q.gens c}∩{c | ListRegular L c} := by
      ext c; simp [ListRegular]
    rw [he]
    exact (dense_regular q.gens (hL q (by simp))).inter_of_isOpen_left
      (ih (fun r hr=>hL r (by simp [hr]))) (isOpen_regular q.gens)

end BarvinokCount.ShortFormula.Proof
-- End RegularDense

-- Begin SigmaTransfer

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d : ℕ}

lemma sigma_equality_remove_extra (L M E : List (ConeTerm d))
    (hL : ∀ q∈L,IsSimpleGens q.gens) (hM : ∀ q∈M,IsSimpleGens q.gens)
    (hE : ∀ q∈E,IsSimpleGens q.gens)
    (he : ∀ c,ListRegular L c→ListRegular M c→ListRegular E c→sigmaTermSum L c=sigmaTermSum M c)
    (c : Fin d → ℝ) (hLc : ListRegular L c) (hMc : ListRegular M c) :
    sigmaTermSum L c=sigmaTermSum M c := by
  let S := {c | ListRegular L c}∩{c | ListRegular M c}∩{c | ListRegular E c}
  have hS : Dense S := ((dense_listRegular L hL).inter_of_isOpen_left
    (dense_listRegular M hM) (isOpen_listRegular L)).inter_of_isOpen_right
      (dense_listRegular E hE) (isOpen_listRegular E)
  have hf : Continuous (fun c=>listNumerator L c*listDenominator M c) :=
    continuous_iff_continuousAt.mpr (fun c=>((listNumerator_analytic L c).mul
      (listDenominator_analytic M c)).continuousAt)
  have hg : Continuous (fun c=>listNumerator M c*listDenominator L c) :=
    continuous_iff_continuousAt.mpr (fun c=>((listNumerator_analytic M c).mul
      (listDenominator_analytic L c)).continuousAt)
  have hh : Set.EqOn (fun c=>listNumerator L c*listDenominator M c)
      (fun c=>listNumerator M c*listDenominator L c) S := by
    intro c hc
    have hc' : (ListRegular L c ∧ ListRegular M c) ∧ ListRegular E c := hc
    have hv := he c hc'.1.1 hc'.1.2 hc'.2
    rw [sigmaTermSum_fraction L c hc'.1.1,sigmaTermSum_fraction M c hc'.1.2] at hv
    exact (div_eq_div_iff (listDenominator_ne_zero L c hc'.1.1)
      (listDenominator_ne_zero M c hc'.1.2)).mp hv
  have hall := hh.closure hf hg (hS c)
  rw [sigmaTermSum_fraction L c hLc,sigmaTermSum_fraction M c hMc]
  exact (div_eq_div_iff (listDenominator_ne_zero L c hLc)
    (listDenominator_ne_zero M c hMc)).mpr hall

lemma sigma_equality_trans (L M E : List (ConeTerm d))
    (hL : ∀ q∈L,IsSimpleGens q.gens) (hM : ∀ q∈M,IsSimpleGens q.gens)
    (hE : ∀ q∈E,IsSimpleGens q.gens)
    (hLM : ∀ c,ListRegular L c→ListRegular M c→sigmaTermSum L c=sigmaTermSum M c)
    (hME : ∀ c,ListRegular M c→ListRegular E c→sigmaTermSum M c=sigmaTermSum E c) :
    ∀ c,ListRegular L c→ListRegular E c→sigmaTermSum L c=sigmaTermSum E c := by
  exact sigma_equality_remove_extra L E M hL hE hM
    (fun c hLc hEc hMc=>(hLM c hLc hMc).trans (hME c hMc hEc))

end BarvinokCount.ShortFormula.Proof
-- End SigmaTransfer

-- Begin ListRefinement

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d : ℕ}

lemma listRegular_scale_iff (L : List (ConeTerm d)) (r : ℤ) (c : Fin d → ℝ) :
    ListRegular (L.map (fun q=>q.scale r)) c ↔ ListRegular L c := by
  simp only [ListRegular,List.mem_map]
  constructor
  · intro h q hq
    exact h (q.scale r) ⟨q,hq,rfl⟩
  · rintro h _ ⟨q,hq,rfl⟩
    exact h q hq

lemma listRegular_append_iff (L M : List (ConeTerm d)) (c : Fin d → ℝ) :
    ListRegular (L++M) c ↔ ListRegular L c ∧ ListRegular M c := by
  simp only [ListRegular,List.mem_append,or_imp,forall_and]

lemma refine_cone_list (L : List (ConeTerm d)) (B : ℕ) (R : ℝ)
    (hex : ∀ q∈L,∃ K : List (ConeTerm d),K.length≤B ∧
      (∀ r∈K,IsSimpleGens r.gens) ∧ (∀ r∈K,(coneIndex r.gens:ℝ)≤R) ∧
      (∀ x,(cone q.gens).indicator (fun _=>(1:ℝ)) x=coneTermSum K x) ∧
      (∀ c,IsRegular q.gens c→ListRegular K c→sigma q.gens c=sigmaTermSum K c)) :
    ∃ M : List (ConeTerm d),M.length≤L.length*B ∧
      (∀ r∈M,IsSimpleGens r.gens) ∧ (∀ r∈M,(coneIndex r.gens:ℝ)≤R) ∧
      (∀ x,coneTermSum L x=coneTermSum M x) ∧
      (∀ c,ListRegular L c→ListRegular M c→sigmaTermSum L c=sigmaTermSum M c) := by
  induction L with
  | nil => exact ⟨[],by simp,by simp,by simp,fun _=>rfl,fun _ _ _=>rfl⟩
  | cons q L ih =>
    obtain ⟨K,hKlen,hKs,hKi,hKid,hKsig⟩ := hex q (by simp)
    obtain ⟨M,hMlen,hMs,hMi,hMid,hMsig⟩ := ih (fun r hr=>hex r (by simp [hr]))
    refine ⟨K.map (fun r=>r.scale q.coeff)++M,?_,?_,?_,?_,?_⟩
    · simp only [List.length_append,List.length_map,List.length_cons]
      calc
        K.length+M.length≤B+L.length*B := Nat.add_le_add hKlen hMlen
        _ = (L.length+1)*B := by ring
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
        exact hKs s hs
      · exact hMs r hr
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
        exact hKi s hs
      · exact hMi r hr
    · intro x
      rw [coneTermSum_append,coneTermSum_scale]
      change q.eval x+coneTermSum L x=_
      rw [ConeTerm.eval,hKid,hMid]
    · intro c hLc hMc
      obtain ⟨hKc,hMc⟩ := (listRegular_append_iff _ _ c).mp hMc
      have hKc' := (listRegular_scale_iff K q.coeff c).mp hKc
      have hqc := hLc q (by simp)
      have htc : ListRegular L c := fun r hr=>hLc r (by simp [hr])
      rw [sigmaTermSum_append,sigmaTermSum_scale]
      change (q.coeff:ℝ)*sigma q.gens c+sigmaTermSum L c=_
      rw [hKsig c hqc hKc',hMsig c htc hMc]

end BarvinokCount.ShortFormula.Proof
-- End ListRefinement

-- Begin IterationBound

namespace BarvinokCount.ShortFormula.Proof

lemma iteration_ratio {d : ℕ} (hd : 2≤d) :
    0<((d:ℝ)-1)/d ∧ ((d:ℝ)-1)/d<1 := by
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  constructor
  · exact div_pos (by linarith) (by linarith)
  · apply (div_lt_one (by positivity)).mpr
    linarith

lemma iteration_log_gap {d : ℕ} (hd : 2≤d) :
    0<Real.log (d:ℝ)-Real.log ((d:ℝ)-1) := by
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  exact sub_pos.mpr (Real.log_lt_log (by linarith) (by linarith))

lemma iteration_scalar_bound {d N : ℕ} (hd : 2≤d) (hN : 1<N) :
    (N:ℝ)^((((d:ℝ)-1)/d)^iterCount d N)≤(1.9:ℝ) := by
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  have hN' : (1:ℝ)<N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := lt_trans zero_lt_one hN'
  have hlogN : 0<Real.log (N:ℝ) := Real.log_pos hN'
  have hlog19 : 0<Real.log (1.9:ℝ) := Real.log_pos (by norm_num)
  have hgap := iteration_log_gap hd
  have hq := (iteration_ratio hd).1
  have hceil : (-Real.log (Real.log (1.9:ℝ))+Real.log (Real.log (N:ℝ))) /
      (Real.log (d:ℝ)-Real.log ((d:ℝ)-1)) ≤ (iterCount d N:ℝ) := by
    rw [iterCount,if_neg (by omega)]
    exact Nat.le_ceil _
  have hb := (div_le_iff₀ hgap).mp hceil
  have hlogq : Real.log (((d:ℝ)-1)/d)=-(Real.log (d:ℝ)-Real.log ((d:ℝ)-1)) := by
    rw [Real.log_div (by linarith) (by positivity)]
    ring
  have hlog : Real.log (Real.log (N:ℝ)*(((d:ℝ)-1)/d)^iterCount d N) ≤ Real.log (Real.log (1.9:ℝ)) := by
    rw [Real.log_mul hlogN.ne' (pow_pos hq _).ne',Real.log_pow,hlogq]
    nlinarith
  have hm : Real.log (N:ℝ)*(((d:ℝ)-1)/d)^iterCount d N ≤ Real.log (1.9:ℝ) :=
    (Real.log_le_log_iff (mul_pos hlogN (pow_pos hq _)) hlog19).mp hlog
  rw [Real.rpow_def_of_pos hNp]
  calc
    Real.exp (Real.log (N:ℝ)*(((d:ℝ)-1)/d)^iterCount d N) ≤ Real.exp (Real.log (1.9:ℝ)) :=
      Real.exp_le_exp.mpr hm
    _ = (1.9:ℝ) := Real.exp_log (by norm_num)

end BarvinokCount.ShortFormula.Proof
-- End IterationBound

-- Begin ConeIteration

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma iterate_cone (hd : 2≤d) (T : ℕ) (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    ∃ L : List (ConeTerm d), L.length≤(2^d)^T ∧
      (∀ q∈L,IsSimpleGens q.gens) ∧
      (∀ q∈L,(coneIndex q.gens:ℝ)≤(coneIndex u:ℝ)^((((d:ℝ)-1)/d)^T)) ∧
      (∀ x,(cone u).indicator (fun _=>(1:ℝ)) x=coneTermSum L x) ∧
      (∀ c,IsRegular u c→ListRegular L c→sigma u c=sigmaTermSum L c) := by
  induction T generalizing k with
  | zero =>
    refine ⟨[⟨k,u,1⟩],by simp,?_,?_,?_,?_⟩
    · intro q hq
      have he : q=⟨k,u,1⟩ := by simpa using hq
      subst q
      exact hu
    · intro q hq
      have he : q=⟨k,u,1⟩ := by simpa using hq
      subst q
      simp
    · intro x
      simp [coneTermSum,ConeTerm.eval]
    · intro c _ _
      simp [sigmaTermSum,ConeTerm.sigmaEval]
  | succ T ih =>
    obtain ⟨L,hlen,hLs,hLi,hLid,hLsig⟩ := exists_cone_step u hu
    have hex : ∀ q∈L,∃ K : List (ConeTerm d),K.length≤(2^d)^T ∧
        (∀ r∈K,IsSimpleGens r.gens) ∧
        (∀ r∈K,(coneIndex r.gens:ℝ)≤(coneIndex u:ℝ)^((((d:ℝ)-1)/d)^(T+1))) ∧
        (∀ x,(cone q.gens).indicator (fun _=>(1:ℝ)) x=coneTermSum K x) ∧
        (∀ c,IsRegular q.gens c→ListRegular K c→sigma q.gens c=sigmaTermSum K c) := by
      intro q hq
      obtain ⟨K,hlen,hKs,hKi,hKid,hKsig⟩ := ih q.gens (hLs q hq)
      refine ⟨K,hlen,hKs,?_,hKid,hKsig⟩
      intro r hr
      apply (hKi r hr).trans
      calc
        (coneIndex q.gens:ℝ)^((((d:ℝ)-1)/d)^T) ≤
            ((coneIndex u:ℝ)^(((d:ℝ)-1)/d))^((((d:ℝ)-1)/d)^T) :=
          Real.rpow_le_rpow (by positivity) (hLi q hq) (pow_nonneg (iteration_ratio hd).1.le _)
        _ = (coneIndex u:ℝ)^((((d:ℝ)-1)/d)^(T+1)) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg _),pow_succ']
    obtain ⟨M,hMlen,hMs,hMi,hMid,hMsig⟩ := refine_cone_list L ((2^d)^T)
      ((coneIndex u:ℝ)^((((d:ℝ)-1)/d)^(T+1))) hex
    refine ⟨M,?_,hMs,hMi,fun x=>(hLid x).trans (hMid x),?_⟩
    · calc
        M.length≤L.length*(2^d)^T := hMlen
        _≤(2^d)*(2^d)^T := Nat.mul_le_mul_right _ hlen
        _=(2^d)^(T+1) := (pow_succ' _ _).symm
    · let orig : List (ConeTerm d) := [⟨k,u,1⟩]
      have hos : ∀ q∈orig,IsSimpleGens q.gens := by
        intro q hq
        have he : q=⟨k,u,1⟩ := by simpa [orig] using hq
        subst q
        exact hu
      have hsig : ∀ c,ListRegular orig c→ListRegular L c→sigmaTermSum orig c=sigmaTermSum L c := by
        intro c hc hLc
        have hh := hLsig c (hc ⟨k,u,1⟩ (by simp [orig])) hLc
        simpa [orig,sigmaTermSum,ConeTerm.sigmaEval] using hh
      intro c hc hMc
      have hoc : ListRegular orig c := by
        intro q hq
        have he : q=⟨k,u,1⟩ := by simpa [orig] using hq
        subst q
        exact hc
      have hh := sigma_equality_trans orig L M hos hLs hMs hsig hMsig c hoc hMc
      simpa [orig,sigmaTermSum,ConeTerm.sigmaEval] using hh

end BarvinokCount.ShortFormula.Proof
-- End ConeIteration

-- Begin PrimitiveDecomposition

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma primitive_decomposition (hd : 2≤d) (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    ∃ L : List (ConeTerm d), L.length≤(2^d)^iterCount d (coneIndex u) ∧
      ListPrimitive L ∧
      (∀ x,(cone u).indicator (fun _=>(1:ℝ)) x=coneTermSum L x) ∧
      (∀ c,IsRegular u c→ListRegular L c→sigma u c=sigmaTermSum L c) := by
  obtain ⟨L,hlen,hLs,hLi,hLid,hLsig⟩ := iterate_cone hd (iterCount d (coneIndex u)) u hu
  refine ⟨L,hlen,?_,hLid,hLsig⟩
  intro q hq
  apply (primitive_iff_index_one q.gens (hLs q hq)).mpr
  have hp := coneIndex_pos q.gens
  have hb := hLi q hq
  by_cases hN : coneIndex u≤1
  · have hn : coneIndex u=1 := by have := coneIndex_pos u; omega
    rw [hn,Nat.cast_one,Real.one_rpow] at hb
    have hqle : coneIndex q.gens≤1 := by exact_mod_cast hb
    omega
  · have hm := hb.trans (iteration_scalar_bound hd (by omega))
    have hlt : (coneIndex q.gens:ℝ)<2 := lt_of_le_of_lt hm (by norm_num)
    have hlt' : coneIndex q.gens<2 := by exact_mod_cast hlt
    omega

end BarvinokCount.ShortFormula.Proof
-- End PrimitiveDecomposition

-- Begin BarycentricBasic

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

noncomputable def baryValue {I : Type*} [Fintype I] {d : ℕ}
    (v : I → Fin d → ℤ) (a : I → ℝ) : Fin d → ℝ :=
  ∑ i, a i • castVec (v i)

theorem baryValue_injective {I : Type*} [Fintype I] {d : ℕ}
    (v : I → Fin d → ℤ) (hv : AffineIndependent ℝ (fun i => castVec (v i)))
    {a b : I → ℝ} (ha : ∑ i,a i=1) (hb : ∑ i,b i=1)
    (h : baryValue v a = baryValue v b) : a=b := by
  apply (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ _).mp hv a b ha hb
  simpa [Finset.affineCombination_eq_linear_combination _ _ _ ha,
    Finset.affineCombination_eq_linear_combination _ _ _ hb, baryValue] using h

noncomputable def residueLift {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (j : I) : I → ℝ := r + Pi.single j (1-∑ i,r i)

@[simp] theorem residueLift_sum {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (j : I) : ∑ i,residueLift r j i=1 := by
  simp [residueLift, Finset.sum_add_distrib]

@[simp] theorem residueLift_same {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (j : I) : residueLift r j j = r j+1-∑ i,r i := by
  simp [residueLift]; ring

@[simp] theorem residueLift_ne {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) {i j : I} (h : i ≠ j) : residueLift r j i = r i := by
  simp [residueLift, Pi.single_eq_of_ne h]

theorem baryValue_residueLift {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (v : I → Fin d → ℤ) (r : I → ℝ) (j : I) :
    baryValue v (residueLift r j) = baryValue v r+(1-∑ i,r i) • castVec (v j) := by
  simp [baryValue,residueLift,add_smul,Finset.sum_add_distrib,Pi.single_apply]

theorem residueLift_fract {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i < 1) (C : ℤ)
    (hC : ∑ i,r i=(C:ℝ)) (j i : I) : Int.fract (residueLift r j i)=r i := by
  by_cases h : i=j
  · subst i
    rw [residueLift_same,hC]
    have he : r j+1-(C:ℝ)=r j+(1-C:ℤ) := by push_cast; ring
    rw [he,Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr (hr j)
  · rw [residueLift_ne r h]
    exact Int.fract_eq_self.mpr (hr i)

end BarvinokCount.ShortFormula.Proof
-- End BarycentricBasic

-- Begin BarycentricResidue

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

def BaryIntegral {I : Type*} [Fintype I] {d : ℕ} (v : I → Fin d → ℤ) (a : I → ℝ) : Prop :=
  ∃ z : Fin d → ℤ, castVec z = baryValue v a

def BaryBox {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ) (j : Fin (k+1)) :=
  {a : Fin (k+1) → ℝ // (∑ i,a i=1) ∧
    (∀ i, i ≠ j → 0 ≤ a i ∧ a i < 1) ∧ BaryIntegral v a}

def BaryResidue {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ) :=
  {r : Fin (k+1) → ℝ // (∀ i,0 ≤ r i ∧ r i < 1) ∧
    (∃ C : ℤ, ∑ i,r i=(C:ℝ)) ∧ ∀ j,BaryIntegral v (residueLift r j)}

theorem weights_eq_of_except {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ℝ) (j : I) (hs : ∑ i,a i=∑ i,b i)
    (he : ∀ i,i≠j → a i=b i) : a=b := by
  have hj : a j=b j := by
    have hd : ∑ i,(a i-b i)=a j-b j := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        rw [he i hij,sub_self]
      · simp
    rw [Finset.sum_sub_distrib,hs,sub_self] at hd
    linarith
  funext i
  by_cases h : i=j
  · simpa [h] using hj
  · exact he i h

theorem integral_residue_transfer {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (v : I → Fin d → ℤ) (r : I → ℝ) (C : ℤ) (hC : ∑ i,r i=(C:ℝ))
    (j l : I) (hj : BaryIntegral v (residueLift r j)) :
    BaryIntegral v (residueLift r l) := by
  obtain ⟨z,hz⟩ := hj
  refine ⟨z+(1-C) • (v l-v j),?_⟩
  rw [castVec_add,castVec_zsmul,castVec_sub,hz]
  simp only [baryValue_residueLift,hC,Int.cast_sub,Int.cast_one]
  module

noncomputable def boxResidue {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (j : Fin (k+1)) (a : BaryBox v j) : BaryResidue v := by
  let r := fun i => Int.fract (a.1 i)
  have hr : ∀ i,0 ≤ r i ∧ r i < 1 := fun i =>
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  have hC : ∑ i,r i=((1-∑ i,⌊a.1 i⌋):ℤ) := by
    simp only [r,Int.fract,Finset.sum_sub_distrib,← Int.cast_sum]
    rw [a.2.1]
    push_cast
    rfl
  have ha : residueLift r j=a.1 := by
    apply weights_eq_of_except _ _ j ((residueLift_sum r j).trans a.2.1.symm)
    intro i hij
    rw [residueLift_ne r hij]
    exact Int.fract_eq_self.mpr (a.2.2.1 i hij)
  refine ⟨r,hr,⟨1-∑ i,⌊a.1 i⌋,hC⟩,fun l => ?_⟩
  apply integral_residue_transfer v r _ hC j l
  simpa [ha] using a.2.2.2

noncomputable def residueBox {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (j : Fin (k+1)) (r : BaryResidue v) : BaryBox v j :=
  ⟨residueLift r.1 j,residueLift_sum _ _,
    fun i hi => by rw [residueLift_ne _ hi]; exact r.2.1 i,r.2.2.2 j⟩

noncomputable def residueBoxEquiv {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (j : Fin (k+1)) : BaryResidue v ≃ BaryBox v j where
  toFun := residueBox v j
  invFun := boxResidue v j
  left_inv r := by
    apply Subtype.ext
    funext i
    obtain ⟨C,hC⟩ := r.2.2.1
    exact residueLift_fract r.1 r.2.1 C hC j i
  right_inv a := by
    apply Subtype.ext
    apply weights_eq_of_except _ _ j ((residueLift_sum _ j).trans a.2.1.symm)
    intro i hij
    change residueLift (fun l => Int.fract (a.1 l)) j i=a.1 i
    rw [residueLift_ne _ hij]
    exact Int.fract_eq_self.mpr (a.2.2.1 i hij)

end BarvinokCount.ShortFormula.Proof
-- End BarycentricResidue

-- Begin BarycentricEdges

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

noncomputable def edgeWeights {k : ℕ} (j : Fin (k+1)) (a : Fin k → ℝ) : Fin (k+1) → ℝ :=
  j.insertNth (1-∑ i,a i) a

@[simp] theorem edgeWeights_sum {k : ℕ} (j : Fin (k+1)) (a : Fin k → ℝ) :
    ∑ i,edgeWeights j a i=1 := by
  rw [Fin.sum_univ_succAbove _ j]
  simp [edgeWeights]

theorem baryValue_edgeWeights {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (j : Fin (k+1)) (a : Fin k → ℝ) :
    baryValue v (edgeWeights j a) = castVec (v j)+∑ i,a i • castVec (edgeGens v j i) := by
  unfold baryValue
  rw [Fin.sum_univ_succAbove _ j]
  simp only [edgeWeights, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    edgeGens, castVec_sub, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  module

theorem edgeWeights_unique {k : ℕ} (j : Fin (k+1)) (a : Fin (k+1) → ℝ)
    (ha : ∑ i,a i=1) : edgeWeights j (fun i => a (j.succAbove i))=a := by
  funext i
  induction i using j.succAboveCases
  · have h := Fin.sum_univ_succAbove a j
    simp only [edgeWeights, Fin.insertNth_apply_same]
    linarith
  · simp [edgeWeights]

theorem edgeGens_simple {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) (j : Fin (k+1)) :
    IsSimpleGens (edgeGens v j) := by
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ _ j).mp hv
  let e : Fin k ↪ {i : Fin (k+1) // i ≠ j} :=
    ⟨fun i => ⟨j.succAbove i,Fin.succAbove_ne j i⟩,fun i l h =>
      Fin.succAbove_right_injective (congrArg Subtype.val h)⟩
  convert h.comp e e.injective using 1
  simp only [IsSimpleGens, edgeGens,castVec_sub,Function.comp_def]
  rfl

end BarvinokCount.ShortFormula.Proof
-- End BarycentricEdges

-- Begin BarycentricSimplex

open scoped BigOperators
open Set
namespace BarvinokCount.ShortFormula.Proof

theorem simplex_mem_iff_weights {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ) (x : Fin d → ℝ) :
    x ∈ simplex v ↔ ∃ a : Fin (k+1) → ℝ,
      (∀ i,0 ≤ a i) ∧ (∑ i,a i=1) ∧ baryValue v a=x := by
  have he : simplex v = (Fintype.linearCombination ℝ (fun i => castVec (v i))) ''
      stdSimplex ℝ (Fin (k+1)) := by
    rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull,
      ← Set.range_comp]
    ext y
    simp [Function.comp_def,Fintype.linearCombination_apply, simplex]
  rw [he]
  simp only [Set.mem_image, stdSimplex, Set.mem_ofPred_eq, Fintype.linearCombination_apply, baryValue]
  tauto

def BarySimplex {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ) :=
  {a : Fin (k+1) → ℝ // (∑ i,a i=1) ∧ (∀ i,0 ≤ a i) ∧ BaryIntegral v a}

noncomputable def barySimplexEquiv {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) :
    BarySimplex v ≃ {z : Fin d → ℤ // castVec z ∈ simplex v} := by
  let F : BarySimplex v → {z : Fin d → ℤ // castVec z ∈ simplex v} :=
    fun a => ⟨a.2.2.2.choose,(simplex_mem_iff_weights v _).mpr
      ⟨a.1,a.2.2.1,a.2.1,a.2.2.2.choose_spec.symm⟩⟩
  refine Equiv.ofBijective F ⟨?_,?_⟩
  · intro a b h
    apply Subtype.ext
    apply baryValue_injective v hv a.2.1 b.2.1
    exact a.2.2.2.choose_spec.symm.trans
      ((congrArg (fun z => castVec z.1) h).trans b.2.2.2.choose_spec)
  · rintro ⟨z,hz⟩
    obtain ⟨a,ha,hs,he⟩ := (simplex_mem_iff_weights v _).mp hz
    have hi : BaryIntegral v a := ⟨z,he.symm⟩
    refine ⟨⟨a,hs,ha,hi⟩,?_⟩
    apply Subtype.ext
    exact castVec_injective (hi.choose_spec.trans he)

theorem simplex_weight_le_one {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (a : BarySimplex v) (j : Fin (k+1)) : a.1 j ≤ 1 := by
  exact (Finset.single_le_sum (fun i _ => a.2.2.1 i) (Finset.mem_univ j)).trans_eq a.2.1

theorem simplex_weight_eq_one {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (a : BarySimplex v) (j : Fin (k+1)) (hj : a.1 j=1) : a.1=Pi.single j 1 := by
  apply weights_eq_of_except _ _ j (by simpa using a.2.1)
  intro i hij
  have h : a.1 i+a.1 j ≤ ∑ l,a.1 l :=
    Finset.add_le_sum (fun l _ => a.2.2.1 l) (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hi : a.1 i=0 := by rw [a.2.1,hj] at h; linarith [a.2.2.1 i]
  simpa [Pi.single_eq_of_ne hij] using hi

end BarvinokCount.ShortFormula.Proof
-- End BarycentricSimplex

-- Begin SupportingCone

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma supportingCone_simplex (v : Fin (k+1) → Fin d → ℤ) (j : Fin (k+1)) :
    supportingCone (simplex v) (castVec (v j))=cone (edgeGens v j) := by
  ext y
  constructor
  · rintro ⟨δ,hδ,hm⟩
    obtain ⟨a,ha,hs,he⟩ := (simplex_mem_iff_weights v _).mp (hm δ hδ le_rfl)
    have hb := baryValue_edgeWeights v j (fun i=>a (j.succAbove i))
    rw [edgeWeights_unique j a hs,he] at hb
    have hy : δ • y=∑ i,a (j.succAbove i) • castVec (edgeGens v j i) := add_left_cancel hb
    refine ⟨fun i=>a (j.succAbove i)/δ,fun i=>div_nonneg (ha _) hδ.le,?_⟩
    have hh := congrArg (fun z : Fin d → ℝ=>δ⁻¹ • z) hy
    simpa only [smul_smul,inv_mul_cancel₀ hδ.ne',one_smul,Finset.smul_sum,div_eq_mul_inv,mul_comm] using hh
  · rintro ⟨a,ha,hy⟩
    let S := ∑ i,a i
    have hS : 0≤S := Finset.sum_nonneg (fun i _=>ha i)
    have hp : 0<S+1 := by linarith
    refine ⟨1/(S+1),by positivity,?_⟩
    intro δ hδ hδle
    have hb : δ*S≤1 := by
      have hh := (le_div_iff₀ hp).mp hδle
      nlinarith
    apply (simplex_mem_iff_weights v _).mpr
    refine ⟨edgeWeights j (fun i=>δ*a i),?_,edgeWeights_sum _ _,?_⟩
    · intro i
      induction i using j.succAboveCases
      · simp only [edgeWeights,Fin.insertNth_apply_same,← Finset.mul_sum]
        exact sub_nonneg.mpr hb
      · simp only [edgeWeights,Fin.insertNth_apply_succAbove]
        exact mul_nonneg hδ.le (ha _)
    · rw [baryValue_edgeWeights,hy]
      simp only [Finset.smul_sum,mul_smul]

end BarvinokCount.ShortFormula.Proof
-- End SupportingCone

-- Begin FinalDirection

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma eq_of_dense_continuousAt {X : Type*} [TopologicalSpace X] (S : Set X) (hS : Dense S)
    (f g : X → ℝ) (x : X) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (he : Set.EqOn f g S) : f x=g x := by
  have : (𝓝[S] x).NeBot := mem_closure_iff_clusterPt.mp (hS x)
  exact tendsto_nhds_unique_of_eventuallyEq hf.continuousWithinAt hg.continuousWithinAt
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)

lemma sigma_continuousAt (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ) (hc : IsRegular u c) :
    ContinuousAt (sigma u) c := by
  have he : sigma u=(fun c=>sigmaNumerator u c/sigmaDenominator u c) := funext (sigma_fraction u)
  rw [he]
  exact (sigmaNumerator_analytic u c).continuousAt.div (sigmaDenominator_analytic u c).continuousAt
    (sigmaDenominator_ne_zero u c hc)

lemma sigmaTermSum_continuousAt (L : List (ConeTerm d)) (c : Fin d → ℝ) (hc : ListRegular L c) :
    ContinuousAt (sigmaTermSum L) c := by
  induction L with
  | nil => exact continuousAt_const
  | cons q L ih =>
    have hq := (continuousAt_const (y := (q.coeff:ℝ))).mul
      (sigma_continuousAt q.gens c (hc q (by simp)))
    exact hq.add (ih (fun r hr=>hc r (by simp [hr])))

lemma dense_vertexRegular (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun j=>castVec (v j))) :
    Dense {c | ∀ j,IsRegular (edgeGens v j) c} := by
  have he : {c | ∀ j,IsRegular (edgeGens v j) c}=⋂ j,{c | IsRegular (edgeGens v j) c} := by
    ext c; simp
  rw [he]
  exact dense_iInter_of_isOpen (fun j=>isOpen_regular _) (fun j=>dense_regular _ (edgeGens_simple v hv j))

lemma final_direction_transfer (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun j=>castVec (v j))) (L : Fin (k+1) → List (ConeTerm d))
    (hLs : ∀ j q,q∈L j→IsSimpleGens q.gens)
    (hLsig : ∀ j c,IsRegular (edgeGens v j) c→ListRegular (L j) c→
      sigma (edgeGens v j) c=sigmaTermSum (L j) c)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f)
    (hbrion : ∀ c,(∀ j,IsRegular (edgeGens v j) c)→
      f c=∑ j,Real.exp (c ⬝ᵥ castVec (v j))*sigma (edgeGens v j) c)
    (c : Fin d → ℝ) (hc : ∀ j,ListRegular (L j) c) :
    f c=∑ j,Real.exp (c ⬝ᵥ castVec (v j))*sigmaTermSum (L j) c := by
  let S := {c | ∀ j,IsRegular (edgeGens v j) c}∩{c | ∀ j,ListRegular (L j) c}
  have he : {c | ∀ j,ListRegular (L j) c}=⋂ j,{c | ListRegular (L j) c} := by ext c; simp
  have hfinal : Dense {c | ∀ j,ListRegular (L j) c} := by
    rw [he]
    exact dense_iInter_of_isOpen (fun j=>isOpen_listRegular _) (fun j=>dense_listRegular _ (hLs j))
  have hfo : IsOpen {c | ∀ j,ListRegular (L j) c} := by
    rw [he]
    exact isOpen_iInter_of_finite (fun j=>isOpen_listRegular _)
  have hS : Dense S := (dense_vertexRegular v hv).inter_of_isOpen_right hfinal hfo
  apply eq_of_dense_continuousAt S hS f (fun c=>∑ j,Real.exp (c ⬝ᵥ castVec (v j))*sigmaTermSum (L j) c) c
    hf.continuousAt
  · apply tendsto_finsetSum
    intro j _
    exact (analytic_dot_exp (castVec (v j)) c).continuousAt.mul
      (sigmaTermSum_continuousAt (L j) c (hc j))
  · intro x hx
    have hx' : (∀ j,IsRegular (edgeGens v j) x) ∧ (∀ j,ListRegular (L j) x) := hx
    rw [hbrion x hx'.1]
    apply Finset.sum_congr rfl
    intro j _
    rw [hLsig j x (hx'.1 j) (hx'.2 j)]

end BarvinokCount.ShortFormula.Proof
-- End FinalDirection

-- Begin ListIndexing

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof
variable {d : ℕ}

lemma coneTermSum_indexed (L : List (ConeTerm d)) (x : Fin d → ℝ) :
    coneTermSum L x=∑ i : Fin L.length,(L.get i).eval x := by
  have h : L=List.ofFn L.get := (List.ofFn_get L).symm
  conv_lhs => rw [h]
  simp only [coneTermSum,List.map_ofFn,List.sum_ofFn,Function.comp_def]

lemma sigmaTermSum_indexed (L : List (ConeTerm d)) (c : Fin d → ℝ) :
    sigmaTermSum L c=∑ i : Fin L.length,(L.get i).sigmaEval c := by
  have h : L=List.ofFn L.get := (List.ofFn_get L).symm
  conv_lhs => rw [h]
  simp only [sigmaTermSum,List.map_ofFn,List.sum_ofFn,Function.comp_def]

lemma listRegular_indexed_iff (L : List (ConeTerm d)) (c : Fin d → ℝ) :
    ListRegular L c ↔ ∀ i : Fin L.length,IsRegular (L.get i).gens c := by
  constructor
  · intro h i
    exact h _ (List.get_mem L i)
  · intro h q hq
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hq
    rw [← hi]
    exact h i

end BarvinokCount.ShortFormula.Proof
-- End ListIndexing

-- Begin BarycentricBox

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

noncomputable def baryBoxEquiv {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) (j : Fin (k+1)) :
    BaryBox v j ≃ {z : Fin d → ℤ // castVec z ∈ halfOpenBox (edgeGens v j)} := by
  have hid (a : BaryBox v j) : baryValue v a.1 = castVec (v j)+
      ∑ i,a.1 (j.succAbove i) • castVec (edgeGens v j i) := by
    rw [← edgeWeights_unique j a.1 a.2.1]
    simpa [edgeWeights] using baryValue_edgeWeights v j (fun i => a.1 (j.succAbove i))
  let F : BaryBox v j → {z : Fin d → ℤ // castVec z ∈ halfOpenBox (edgeGens v j)} :=
    fun a => ⟨a.2.2.2.choose-v j,fun i => a.1 (j.succAbove i),
      fun i => a.2.2.1 _ (Fin.succAbove_ne _ _),by
        rw [castVec_sub,a.2.2.2.choose_spec,hid]
        module⟩
  refine Equiv.ofBijective F ⟨?_,?_⟩
  · intro a b hab
    apply Subtype.ext
    apply baryValue_injective v hv a.2.1 b.2.1
    have h := congrArg (fun z => castVec z.1) hab
    change castVec (a.2.2.2.choose-v j)=castVec (b.2.2.2.choose-v j) at h
    simpa only [castVec_sub,a.2.2.2.choose_spec,b.2.2.2.choose_spec,
      sub_left_inj] using h
  · rintro ⟨z,c,hc,hz⟩
    have hb : BaryIntegral v (edgeWeights j c) := by
      refine ⟨v j+z,?_⟩
      rw [castVec_add,baryValue_edgeWeights,hz]
    let a : BaryBox v j := ⟨edgeWeights j c,edgeWeights_sum j c,by
      intro i hi
      obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hi
      simpa [edgeWeights] using hc l,hb⟩
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply castVec_injective
    change castVec (hb.choose-v j)=castVec z
    rw [castVec_sub,hb.choose_spec,baryValue_edgeWeights,← hz]
    module

theorem baryBox_finite {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) (j : Fin (k+1)) :
    Finite (BaryBox v j) := by
  let : Finite {z : Fin d → ℤ // castVec z ∈ halfOpenBox (edgeGens v j)} :=
    (finite_box_lattice (edgeGens v j)).to_subtype
  exact Finite.of_equiv _ (baryBoxEquiv v hv j).symm

theorem baryResidue_finite {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) : Finite (BaryResidue v) := by
  let := baryBox_finite v hv 0
  exact Finite.of_equiv _ (residueBoxEquiv v 0).symm

end BarvinokCount.ShortFormula.Proof
-- End BarycentricBox

-- Begin SimplexResiduePartition

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

noncomputable def vertexBary {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (j : Fin (k+1)) : BarySimplex v :=
  ⟨Pi.single j 1,by simp,fun i => by simp [Pi.single_apply]; positivity,
    ⟨v j,by simp [baryValue,Pi.single_apply]⟩⟩

noncomputable def simplexResidueBary {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (r : {r : BaryResidue v // ∑ i,r.1 i=1}) : BarySimplex v :=
  ⟨r.1.1,r.2,fun i => (r.1.2.1 i).1,by
    have h := r.1.2.2.2 0
    simpa [residueLift,r.2] using h⟩

noncomputable def simplexResidueEquiv {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ) :
    (Fin (k+1) ⊕ {r : BaryResidue v // ∑ i,r.1 i=1}) ≃ BarySimplex v := by
  let F : (Fin (k+1) ⊕ {r : BaryResidue v // ∑ i,r.1 i=1}) → BarySimplex v :=
    Sum.elim (vertexBary v) (simplexResidueBary v)
  refine Equiv.ofBijective F ⟨?_,?_⟩
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        have hh := congrArg (fun a : BarySimplex v => a.1 i) h
        by_cases hij : i=j
        · exact congrArg Sum.inl hij
        · simp [F,vertexBary,Pi.single_eq_of_ne hij] at hh
      | inr r =>
        have hh := congrArg (fun a : BarySimplex v => a.1 i) h
        change (Pi.single i (1:ℝ) : Fin (k+1) → ℝ) i=r.1.1 i at hh
        simp only [Pi.single_eq_same] at hh
        exact False.elim ((r.1.2.1 i).2.ne hh.symm)
    | inr r =>
      cases y with
      | inl j =>
        have hh := congrArg (fun a : BarySimplex v => a.1 j) h
        change r.1.1 j=(Pi.single j (1:ℝ) : Fin (k+1) → ℝ) j at hh
        simp only [Pi.single_eq_same] at hh
        exact False.elim ((r.1.2.1 j).2.ne hh)
      | inr s =>
        apply congrArg Sum.inr
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun a : BarySimplex v => a.1) h
  · intro a
    by_cases h : ∃ j,a.1 j=1
    · obtain ⟨j,hj⟩ := h
      exact ⟨Sum.inl j,Subtype.ext (simplex_weight_eq_one v a j hj).symm⟩
    · have hr : ∀ i,0 ≤ a.1 i ∧ a.1 i < 1 := by
        intro i
        exact ⟨a.2.2.1 i,lt_of_le_of_ne (simplex_weight_le_one v a i)
          (fun hi => h ⟨i,hi⟩)⟩
      let r : BaryResidue v := ⟨a.1,hr,⟨1,by simpa using a.2.1⟩,fun j => by
        simpa [residueLift,a.2.1] using a.2.2.2⟩
      exact ⟨Sum.inr ⟨r,a.2.1⟩,rfl⟩

end BarvinokCount.ShortFormula.Proof
-- End SimplexResiduePartition

-- Begin ResidueDegree

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

noncomputable def residueDegree {d k : ℕ} {v : Fin (k+1) → Fin d → ℤ}
    (r : BaryResidue v) : ℕ := r.2.2.1.choose.toNat

theorem residueDegree_sum {d k : ℕ} {v : Fin (k+1) → Fin d → ℤ}
    (r : BaryResidue v) : ∑ i,r.1 i = (residueDegree r : ℝ) := by
  have hc := r.2.2.1.choose_spec
  have hn : 0 ≤ r.2.2.1.choose := by
    have h : (0 : ℝ) ≤ ∑ i,r.1 i := Finset.sum_nonneg (fun i _ => (r.2.1 i).1)
    rw [hc] at h
    exact_mod_cast h
  rw [hc,residueDegree]
  exact_mod_cast (Int.toNat_of_nonneg hn).symm

theorem residueDegree_le {d k : ℕ} {v : Fin (k+1) → Fin d → ℤ}
    (r : BaryResidue v) : residueDegree r ≤ k := by
  have h : ∑ i,r.1 i < ∑ _ : Fin (k+1),(1:ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => (r.2.1 i).2)
  rw [residueDegree_sum] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    Nat.cast_add,Nat.cast_one] at h
  have hh : residueDegree r < k+1 := by exact_mod_cast h
  omega

noncomputable def zeroResidue {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ) : BaryResidue v :=
  ⟨0,fun _ => by norm_num,⟨0,by simp⟩,fun j =>
    ⟨v j,by simp [residueLift,baryValue,Pi.single_apply]⟩⟩

theorem residueDegree_zero_iff {d k : ℕ} {v : Fin (k+1) → Fin d → ℤ}
    (r : BaryResidue v) : residueDegree r=0 ↔ r=zeroResidue v := by
  constructor
  · intro h
    apply Subtype.ext
    funext i
    have hs : ∑ j,r.1 j=0 := by rw [residueDegree_sum,h]; norm_num
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (r.2.1 j).1)).mp hs i (Finset.mem_univ i)
  · rintro rfl
    have h := residueDegree_sum (zeroResidue v)
    simpa [zeroResidue] using h.symm

end BarvinokCount.ShortFormula.Proof
-- End ResidueDegree

-- Begin SimplexResidueSum

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

theorem simplex_exp_residue_sum {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) (c : Fin d → ℝ) :
    (∑ᶠ z ∈ {z : Fin d → ℤ | castVec z ∈ simplex v}, Real.exp (c ⬝ᵥ castVec z)) =
      (∑ j,Real.exp (c ⬝ᵥ castVec (v j))) +
      ∑ᶠ r : BaryResidue v, if residueDegree r=1 then Real.exp (c ⬝ᵥ baryValue v r.1) else 0 := by
  classical
  let := baryResidue_finite v hv
  let := Fintype.ofFinite (BaryResidue v)
  let := Fintype.ofEquiv (Fin (k+1) ⊕ {r : BaryResidue v // ∑ i,r.1 i=1})
    (simplexResidueEquiv v)
  have hnative : (∑ᶠ z ∈ {z : Fin d → ℤ | castVec z ∈ simplex v}, Real.exp (c ⬝ᵥ castVec z)) =
      ∑ a : BarySimplex v,Real.exp (c ⬝ᵥ baryValue v a.1) := by
    rw [← finsum_set_coe_eq_finsum_mem]
    have he := finsum_comp_equiv (f := fun z : {z : Fin d → ℤ // castVec z ∈ simplex v} => Real.exp (c ⬝ᵥ castVec z.1)) (barySimplexEquiv v hv)
    rw [finsum_eq_sum_of_fintype] at he
    trans ∑ a : BarySimplex v,Real.exp (c ⬝ᵥ castVec (barySimplexEquiv v hv a).1)
    · convert he.symm using 1
      rfl
    apply Finset.sum_congr rfl
    intro a _
    change Real.exp (c ⬝ᵥ castVec a.2.2.2.choose)=_
    rw [a.2.2.2.choose_spec]
  rw [hnative,← (simplexResidueEquiv v).sum_comp,finsum_eq_sum_of_fintype,Fintype.sum_sum_type]
  have hvtx (j : Fin (k+1)) : baryValue v ((simplexResidueEquiv v) (Sum.inl j)).1=castVec (v j) := by
    change baryValue v (Pi.single j 1)=_
    simp [baryValue,Pi.single_apply]
  have hrval (r : {r : BaryResidue v // ∑ i,r.1 i=1}) :
      ((simplexResidueEquiv v) (Sum.inr r)).1=r.1.1 := rfl
  simp only [hvtx,hrval]
  congr 1
  have hsub := Finset.sum_subtype (p := fun r : BaryResidue v => ∑ i,r.1 i=1) (F := inferInstance)
    (Finset.univ.filter (fun r : BaryResidue v => ∑ i,r.1 i=1))
    (fun r => by simp) (fun r : BaryResidue v => Real.exp (c ⬝ᵥ baryValue v r.1))
  rw [Finset.sum_filter] at hsub
  trans ∑ r : BaryResidue v, if (∑ i,r.1 i)=1 then Real.exp (c ⬝ᵥ baryValue v r.1) else 0
  · exact hsub.symm
  apply Finset.sum_congr rfl
  intro r _
  have he : (∑ i,r.1 i=1) ↔ residueDegree r=1 := by
    rw [residueDegree_sum]
    exact_mod_cast Iff.rfl
  simp only [he]

end BarvinokCount.ShortFormula.Proof
-- End SimplexResidueSum

-- Begin ResidueSigma

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

theorem baryBoxEquiv_value {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) (j : Fin (k+1))
    (a : BaryBox v j) : castVec ((baryBoxEquiv v hv j a).1)=baryValue v a.1-castVec (v j) := by
  change castVec (a.2.2.2.choose-v j)=_
  rw [castVec_sub,a.2.2.2.choose_spec]

theorem sigma_vertex_residue {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) (c : Fin d → ℝ)
    (j : Fin (k+1)) :
    Real.exp (c ⬝ᵥ castVec (v j))*sigma (edgeGens v j) c =
      ∑ᶠ r : BaryResidue v, Real.exp (c ⬝ᵥ baryValue v (residueLift r.1 j)) *
        ∏ i, (1-Real.exp (c ⬝ᵥ castVec (edgeGens v j i)))⁻¹ := by
  classical
  let := baryResidue_finite v hv
  let := Fintype.ofFinite (BaryResidue v)
  let e := (residueBoxEquiv v j).trans (baryBoxEquiv v hv j)
  have hs : (∑ᶠ z ∈ {z : Fin d → ℤ | castVec z ∈ halfOpenBox (edgeGens v j)},
      Real.exp (c ⬝ᵥ castVec z)) =
      ∑ r : BaryResidue v, Real.exp (c ⬝ᵥ castVec (e r).1) := by
    rw [← finsum_set_coe_eq_finsum_mem]
    have h := finsum_comp_equiv (f := fun z : {z : Fin d → ℤ // castVec z ∈ halfOpenBox (edgeGens v j)} => Real.exp (c ⬝ᵥ castVec z.1)) e
    rw [finsum_eq_sum_of_fintype] at h
    convert h.symm using 1
    rfl
  rw [sigma,hs,finsum_eq_sum_of_fintype,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have he : castVec (e r).1=baryValue v (residueLift r.1 j)-castVec (v j) :=
    baryBoxEquiv_value v hv j (residueBox v j r)
  rw [he,dotProduct_sub,Real.exp_sub]
  simp only [one_div]
  field_simp

 theorem edge_product_erase {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (c : Fin d → ℝ) (j : Fin (k+1)) :
    (∏ i,(1-Real.exp (c ⬝ᵥ castVec (edgeGens v j i)))⁻¹) =
      ∏ l ∈ Finset.univ.erase j,(1-Real.exp (c ⬝ᵥ castVec (v l)-c ⬝ᵥ castVec (v j)))⁻¹ := by
  classical
  simp only [edgeGens,castVec_sub,dotProduct_sub]
  apply Finset.prod_bij (fun i _ => j.succAbove i)
  · intro i _
    simp [Fin.succAbove_ne]
  · intro i _ l _ h
    exact Fin.succAbove_right_injective h
  · intro l hl
    obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hl).1
    exact ⟨i,Finset.mem_univ i,hi⟩
  · intro i _
    rfl

end BarvinokCount.ShortFormula.Proof
-- End ResidueSigma

-- Begin SimplexInterpolation

open scoped BigOperators
open Polynomial
namespace BarvinokCount.ShortFormula.Proof

theorem interpolation_power_low {k m : ℕ} (y : Fin (k+1) → ℝ)
    (hy : Function.Injective y) (hm : m ≤ k) :
    (∑ j, y j ^ m / ∏ l ∈ Finset.univ.erase j, (y j-y l)) = if m=k then 1 else 0 := by
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := y)
    (P := (X : ℝ[X])^m) hy.injOn (by
      simp only [degree_X_pow, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast (Nat.lt_succ_of_le hm))
  simpa [coeff_X_pow, eq_comm] using h.symm

theorem nodal_coeff_next {k : ℕ} (y : Fin (k+1) → ℝ) :
    (Lagrange.nodal Finset.univ y).coeff k = -∑ i, y i := by
  have h := Polynomial.Monic.nextCoeff_prod Finset.univ
    (fun i => (X : ℝ[X])-C (y i)) (fun i _ => monic_X_sub_C (y i))
  have hd : (Lagrange.nodal Finset.univ y).natDegree = k+1 := by simp
  simpa [Lagrange.nodal, Polynomial.nextCoeff, hd] using h

theorem interpolation_power_next {k : ℕ} (y : Fin (k+1) → ℝ)
    (hy : Function.Injective y) :
    (∑ j, y j ^ (k+1) / ∏ l ∈ Finset.univ.erase j, (y j-y l)) = ∑ j, y j := by
  let P : ℝ[X] := X^(k+1)-Lagrange.nodal Finset.univ y
  have hdeg : P.degree < (k+1 : ℕ) := by
    have h := Polynomial.degree_sub_lt_left
      (p := (X : ℝ[X])^(k+1)) (q := Lagrange.nodal Finset.univ y)
      (by simp) (by simp) (by simp [Lagrange.nodal_monic.leadingCoeff])
    simpa [P] using h
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := y) (P := P)
    hy.injOn (by simpa using hdeg)
  have hev (j : Fin (k+1)) : P.eval (y j) = y j^(k+1) := by
    simp [P, Lagrange.eval_nodal_at_node]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, hev] at h
  rw [show P.coeff k = ∑ i, y i by
    simp [P, nodal_coeff_next, coeff_X_pow]] at h
  exact h.symm

end BarvinokCount.ShortFormula.Proof
-- End SimplexInterpolation

-- Begin ExponentialInterpolation

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

theorem exponential_vertex_term {k C : ℕ} (hC : C ≤ k) (t : Fin (k+1) → ℝ)
    (j : Fin (k+1)) :
    Real.exp ((1-(C:ℝ))*t j) *
      (∏ l ∈ Finset.univ.erase j,(1-Real.exp (t l-t j))⁻¹) =
    Real.exp (t j) ^ (k+1-C) /
      ∏ l ∈ Finset.univ.erase j,(Real.exp (t j)-Real.exp (t l)) := by
  have hp : (∏ l ∈ Finset.univ.erase j,(1-Real.exp (t l-t j))⁻¹) =
      Real.exp (t j)^k / ∏ l ∈ Finset.univ.erase j,(Real.exp (t j)-Real.exp (t l)) := by
    simp_rw [Real.exp_sub,one_sub_div (Real.exp_ne_zero _),inv_div]
    rw [Finset.prod_div_distrib,Finset.prod_const]
    simp
  rw [hp,← mul_div_assoc]
  congr 1
  rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_nat_mul]
  congr 1
  rw [Nat.cast_sub (by omega : C ≤ k+1),Nat.cast_add,Nat.cast_one]
  ring

theorem exponential_interpolation {k C : ℕ} (hC : C ≤ k) (t : Fin (k+1) → ℝ)
    (ht : Function.Injective t) :
    (∑ j,Real.exp ((1-(C:ℝ))*t j) *
      ∏ l ∈ Finset.univ.erase j,(1-Real.exp (t l-t j))⁻¹) =
      if C=0 then ∑ j,Real.exp (t j) else if C=1 then 1 else 0 := by
  simp_rw [exponential_vertex_term hC]
  have hy : Function.Injective (fun j => Real.exp (t j)) := Real.exp_injective.comp ht
  by_cases h0 : C=0
  · subst C
    simpa using interpolation_power_next (fun j => Real.exp (t j)) hy
  · have hm : k+1-C ≤ k := by omega
    rw [interpolation_power_low _ hy hm]
    simp only [h0,if_false]
    have he : k+1-C=k ↔ C=1 := by omega
    simp only [he]

end BarvinokCount.ShortFormula.Proof
-- End ExponentialInterpolation

-- Begin SimplexBrion

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

theorem regular_vertex_injective {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (c : Fin d → ℝ) (hc : ∀ j,IsRegular (edgeGens v j) c) :
    Function.Injective (fun j => c ⬝ᵥ castVec (v j)) := by
  intro j l h
  by_contra hjl
  obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hjl
  have hh := hc l i
  apply hh
  simp only [edgeGens,castVec_sub,dotProduct_sub,hi]
  exact sub_eq_zero.mpr h

theorem residue_vertex_sum {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (c : Fin d → ℝ) (hc : ∀ j,IsRegular (edgeGens v j) c) (r : BaryResidue v) :
    (∑ j,Real.exp (c ⬝ᵥ baryValue v (residueLift r.1 j)) *
      ∏ i,(1-Real.exp (c ⬝ᵥ castVec (edgeGens v j i)))⁻¹) =
    (if residueDegree r=0 then ∑ j,Real.exp (c ⬝ᵥ castVec (v j)) else 0) +
      (if residueDegree r=1 then Real.exp (c ⬝ᵥ baryValue v r.1) else 0) := by
  classical
  simp_rw [baryValue_residueLift,residueDegree_sum,dotProduct_add,dotProduct_smul,
    Real.exp_add,edge_product_erase,smul_eq_mul,mul_assoc]
  rw [← Finset.mul_sum,exponential_interpolation (residueDegree_le r) _
    (regular_vertex_injective v c hc)]
  by_cases h : r=zeroResidue v
  · subst r
    have hz : residueDegree (zeroResidue v)=0 := (residueDegree_zero_iff _).mpr rfl
    simp only [hz,ite_true,Nat.zero_ne_one,ite_false,add_zero]
    simp [zeroResidue,baryValue]
  · have hz : residueDegree r ≠ 0 := fun he => h ((residueDegree_zero_iff r).mp he)
    simp only [hz,if_false,zero_add]
    split_ifs <;> simp

theorem brion_simplex {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun j => castVec (v j))) (c : Fin d → ℝ)
    (hc : ∀ j,IsRegular (edgeGens v j) c) :
    (∑ᶠ z ∈ {z : Fin d → ℤ | castVec z ∈ simplex v},Real.exp (c ⬝ᵥ castVec z)) =
      ∑ j,Real.exp (c ⬝ᵥ castVec (v j))*sigma (edgeGens v j) c := by
  classical
  let := baryResidue_finite v hv
  let := Fintype.ofFinite (BaryResidue v)
  rw [simplex_exp_residue_sum v hv c]
  simp_rw [sigma_vertex_residue v hv c,finsum_eq_sum_of_fintype]
  rw [Finset.sum_comm]
  simp_rw [residue_vertex_sum v c hc]
  rw [Finset.sum_add_distrib]
  simp only [residueDegree_zero_iff]
  simp

end BarvinokCount.ShortFormula.Proof
-- End SimplexBrion

-- Begin SimplexAnalytic

open scoped BigOperators
namespace BarvinokCount.ShortFormula.Proof

theorem finite_simplex_lattice {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) :
    {z : Fin d → ℤ | castVec z ∈ simplex v}.Finite := by
  let := baryResidue_finite v hv
  let : Finite (BarySimplex v) := Finite.of_equiv _ (simplexResidueEquiv v)
  have h : Finite {z : Fin d → ℤ // castVec z ∈ simplex v} :=
    Finite.of_equiv _ (barySimplexEquiv v hv)
  exact Set.finite_coe_iff.mp h

noncomputable def simplexExp {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (c : Fin d → ℝ) : ℝ :=
  ∑ᶠ z ∈ {z : Fin d → ℤ | castVec z ∈ simplex v},Real.exp (c ⬝ᵥ castVec z)

theorem simplexExp_analytic {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) (c : Fin d → ℝ) :
    AnalyticAt ℝ (simplexExp v) c := by
  have he : simplexExp v = fun c =>
      ∑ z ∈ (finite_simplex_lattice v hv).toFinset,Real.exp (c ⬝ᵥ castVec z) := by
    funext x
    exact finsum_mem_eq_finite_toFinset_sum _ (finite_simplex_lattice v hv)
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro z _
  exact analytic_dot_exp (castVec z) c

theorem simplexExp_zero {d k : ℕ} (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun i => castVec (v i))) :
    simplexExp v 0 = (latticeCount (simplex v) : ℝ) := by
  rw [simplexExp,finsum_mem_eq_finite_toFinset_sum _ (finite_simplex_lattice v hv)]
  change _ = ({z : Fin d → ℤ | castVec z ∈ simplex v}.ncard : ℝ)
  rw [Set.ncard_eq_toFinset_card _ (finite_simplex_lattice v hv)]
  simp

end BarvinokCount.ShortFormula.Proof
-- End SimplexAnalytic

-- Begin ExponentialPole

open scoped Topology
open Filter
namespace BarvinokCount.ShortFormula.Proof

theorem exponential_pole_clear (a : ℝ) (ha : a ≠ 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧
      ∀ᶠ t in 𝓝[≠] (0:ℝ), g t = t*(1-Real.exp (t*a))⁻¹ := by
  let f : ℝ → ℝ := fun t => 1-Real.exp (t*a)
  have hf : AnalyticAt ℝ f 0 := by fun_prop
  have hd : HasDerivAt f (-a) 0 := by
    simpa [f] using ((hasDerivAt_id (0:ℝ)).mul_const a).exp.const_sub 1
  have ho : analyticOrderAt f 0=1 :=
    hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [f]) (by rw [hd.deriv]; exact neg_ne_zero.mpr ha)
  obtain ⟨h,hh,hh0,he⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  refine ⟨fun t => (h t)⁻¹,hh.inv hh0,?_⟩
  have hn : ∀ᶠ t in 𝓝 (0:ℝ),h t≠0 := hh.continuousAt.eventually_ne hh0
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,hn.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t ht hnt ht0
  have htne : t≠0 := ht0
  simp only [f,sub_zero,pow_one,smul_eq_mul] at ht
  rw [ht]
  field_simp

end BarvinokCount.ShortFormula.Proof
-- End ExponentialPole

-- Begin SigmaPole

open scoped BigOperators Topology
open Filter
namespace BarvinokCount.ShortFormula.Proof

theorem sigma_pole_clear {d k : ℕ} (u : Fin k → Fin d → ℤ) (v : Fin d → ℤ)
    (c : Fin d → ℝ) (hc : IsRegular u c) :
    ∃ φ : ℝ → ℝ, AnalyticAt ℝ φ 0 ∧
      ∀ᶠ t in 𝓝[≠] (0:ℝ), φ t = t^k *
        (Real.exp ((t • c) ⬝ᵥ castVec v)*sigma u (t • c)) := by
  classical
  choose g hg he using fun i => exponential_pole_clear (c ⬝ᵥ castVec (u i)) (hc i)
  let φ : ℝ → ℝ := fun t => Real.exp (t*(c ⬝ᵥ castVec v))*
    sigmaNumerator u (t • c)*(∏ i,g i t)
  refine ⟨φ,?_,?_⟩
  · have hn : AnalyticAt ℝ (fun t : ℝ => sigmaNumerator u (t • c)) 0 :=
      (sigmaNumerator_analytic u (0 • c)).comp (f := fun t : ℝ => t • c)
        (by fun_prop)
    have hp : AnalyticAt ℝ (fun t : ℝ => ∏ i,g i t) 0 :=
      Finset.analyticAt_fun_prod Finset.univ (fun i _ => hg i)
    exact (show AnalyticAt ℝ (fun t : ℝ => Real.exp (t*(c ⬝ᵥ castVec v))) 0 by fun_prop).mul hn |>.mul hp
  · filter_upwards [Filter.eventually_all.mpr he] with t ht
    have hp : (∏ i,g i t)=t^k*(sigmaDenominator u (t • c))⁻¹ := by
      simp only [ht,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        sigmaDenominator,smul_dotProduct,smul_eq_mul,Finset.prod_inv_distrib]
    change Real.exp (t*(c ⬝ᵥ castVec v))*sigmaNumerator u (t • c)*(∏ i,g i t)=_
    rw [hp,sigma_fraction]
    simp only [smul_dotProduct,smul_eq_mul,div_eq_mul_inv]
    ring

end BarvinokCount.ShortFormula.Proof
-- End SigmaPole

-- Begin LaurentAssembly

open scoped BigOperators Topology
open Filter
namespace BarvinokCount.ShortFormula.Proof

theorem iteratedDeriv_pow_mul_zero (N : ℕ) (F : ℝ → ℝ) (hF : AnalyticAt ℝ F 0) :
    iteratedDeriv N (fun t => t^N*F t) 0 = (N.factorial:ℝ)*F 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hF.contDiffAt]
  simp only [iteratedDeriv_fun_pow_zero]
  simp [mul_ite,ite_mul]

theorem laurent_common_assembly {I : Type*} [Fintype I]
    (N : ℕ) (f φ : I → ℝ → ℝ) (ε : I → ℝ) (F : ℝ → ℝ)
    (hφ : ∀ i,AnalyticAt ℝ (φ i) 0)
    (he : ∀ i,∀ᶠ t in 𝓝[≠] (0:ℝ),φ i t=t^N*f i t)
    (hF : AnalyticAt ℝ F 0)
    (hs : ∀ᶠ t in 𝓝[≠] (0:ℝ),∑ i,ε i*f i t=F t) :
    ∃ a : I → ℝ, (∀ i,IsLaurentConstTerm (f i) (a i)) ∧ ∑ i,ε i*a i=F 0 := by
  classical
  let a := fun i => iteratedDeriv N (φ i) 0 / (N.factorial:ℝ)
  refine ⟨a,fun i => ⟨N,φ i,hφ i,he i,rfl⟩,?_⟩
  have hleft : AnalyticAt ℝ (fun t => ∑ i,ε i*φ i t) 0 :=
    Finset.analyticAt_fun_sum Finset.univ (fun i _ => analyticAt_const.mul (hφ i))
  have hright : AnalyticAt ℝ (fun t => t^N*F t) 0 :=
    (analyticAt_id.pow N).mul hF
  have heq : (fun t => ∑ i,ε i*φ i t) =ᶠ[𝓝[≠] (0:ℝ)] (fun t => t^N*F t) := by
    filter_upwards [Filter.eventually_all.mpr he,hs] with t ht hst
    simp_rw [ht]
    rw [← hst,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heq' := (hleft.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hright.continuousAt).mp heq
  have hd := heq'.iteratedDeriv_eq N
  rw [iteratedDeriv_fun_sum (f := fun i t => ε i*φ i t) (fun i _ => (analyticAt_const.mul (hφ i)).contDiffAt),
    iteratedDeriv_pow_mul_zero N F hF] at hd
  simp only [iteratedDeriv_const_mul_field] at hd
  calc
    (∑ i,ε i*a i) = (∑ i,ε i*iteratedDeriv N (φ i) 0) / (N.factorial:ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a]
      ring
    _ = F 0 := by rw [hd]; field_simp

theorem laurent_finite_assembly {I : Type*} [Fintype I]
    (f : I → ℝ → ℝ) (ε : I → ℝ) (F : ℝ → ℝ)
    (hp : ∀ i,∃ N : ℕ,∃ φ : ℝ → ℝ,AnalyticAt ℝ φ 0 ∧
      ∀ᶠ t in 𝓝[≠] (0:ℝ),φ t=t^N*f i t)
    (hF : AnalyticAt ℝ F 0)
    (hs : ∀ᶠ t in 𝓝[≠] (0:ℝ),∑ i,ε i*f i t=F t) :
    ∃ a : I → ℝ, (∀ i,IsLaurentConstTerm (f i) (a i)) ∧ ∑ i,ε i*a i=F 0 := by
  classical
  choose n φ hφ he using hp
  let N := ∑ i,n i
  have hn (i : I) : n i≤N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  apply laurent_common_assembly N f (fun i t => t^(N-n i)*φ i t) ε F
  · intro i
    exact (analyticAt_id.pow (N-n i)).mul (hφ i)
  · intro i
    filter_upwards [he i] with t ht
    rw [ht,← mul_assoc,← pow_add,Nat.sub_add_cancel (hn i)]
  · exact hF
  · exact hs

end BarvinokCount.ShortFormula.Proof
-- End LaurentAssembly

-- Begin RootAssembly

open scoped BigOperators Topology
namespace BarvinokCount.ShortFormula.Proof
variable {d k : ℕ}

lemma isRegular_smul (u : Fin k → Fin d → ℤ) (c : Fin d → ℝ)
    (hc : IsRegular u c) (t : ℝ) (ht : t≠0) : IsRegular u (t • c) := by
  intro i
  simpa only [smul_dotProduct,smul_eq_mul] using mul_ne_zero ht (hc i)

lemma primitive_formula_constants (v : Fin (k+1) → Fin d → ℤ)
    (hv : AffineIndependent ℝ (fun j=>castVec (v j))) (L : Fin (k+1) → List (ConeTerm d))
    (hLs : ∀ j q,q∈L j→IsSimpleGens q.gens)
    (hLsig : ∀ j c,IsRegular (edgeGens v j) c→ListRegular (L j) c→
      sigma (edgeGens v j) c=sigmaTermSum (L j) c)
    (c : Fin d → ℝ) (hc : ∀ j,ListRegular (L j) c) :
    ∃ R : (j : Fin (k+1)) → Fin (L j).length → ℝ,
      (∀ j i,IsLaurentConstTerm
        (fun t=>Real.exp (t*(c ⬝ᵥ castVec (v j)))*sigma ((L j).get i).gens (t • c)) (R j i)) ∧
      (latticeCount (simplex v):ℝ)=∑ j,∑ i,(((L j).get i).coeff:ℝ)*R j i := by
  classical
  let I := (j : Fin (k+1)) × Fin (L j).length
  let f : I → ℝ → ℝ := fun p t=>Real.exp (t*(c ⬝ᵥ castVec (v p.1)))*
    sigma ((L p.1).get p.2).gens (t • c)
  let ε : I → ℝ := fun p=>(((L p.1).get p.2).coeff:ℝ)
  let F : ℝ → ℝ := fun t=>simplexExp v (t • c)
  have hp : ∀ p : I,∃ n : ℕ,∃ φ : ℝ → ℝ,AnalyticAt ℝ φ 0 ∧
      ∀ᶠ t in 𝓝[≠] (0:ℝ),φ t=t^n*f p t := by
    intro p
    obtain ⟨φ,hφ,he⟩ := sigma_pole_clear ((L p.1).get p.2).gens (v p.1) c
      (hc p.1 _ (List.get_mem _ _))
    refine ⟨((L p.1).get p.2).dim,φ,hφ,?_⟩
    simpa only [f,smul_dotProduct,smul_eq_mul] using he
  have hF : AnalyticAt ℝ F 0 :=
    (simplexExp_analytic v hv (0 • c)).comp (f := fun t : ℝ=>t • c) (by fun_prop)
  have hsum : ∀ᶠ t in 𝓝[≠] (0:ℝ),∑ p : I,ε p*f p t=F t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t≠0 := ht
    have htc : ∀ j,ListRegular (L j) (t • c) := by
      intro j q hq
      exact isRegular_smul q.gens c (hc j q hq) t ht'
    have hh := final_direction_transfer v hv L hLs hLsig (simplexExp v)
      (continuous_iff_continuousAt.mpr (fun x=>(simplexExp_analytic v hv x).continuousAt))
      (fun x hx=>brion_simplex v hv x hx) (t • c) htc
    change (∑ p : (j : Fin (k+1)) × Fin (L j).length,ε p*f p t)=_
    rw [Fintype.sum_sigma]
    rw [show F t=simplexExp v (t • c) from rfl,hh]
    apply Finset.sum_congr rfl
    intro j _
    rw [sigmaTermSum_indexed,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [f,ε,ConeTerm.sigmaEval,smul_dotProduct,smul_eq_mul]
    ring
  obtain ⟨A,hA,hcount⟩ := laurent_finite_assembly f ε F hp hF hsum
  refine ⟨fun j i=>A ⟨j,i⟩,fun j i=>hA ⟨j,i⟩,?_⟩
  simpa only [F,zero_smul,simplexExp_zero v hv,ε,I,Fintype.sum_sigma] using hcount.symm

end BarvinokCount.ShortFormula.Proof

namespace BarvinokCount.ShortFormula
open Proof

theorem latticeCount_eq_short_signed_sum {d k : ℕ} (hd : 2 ≤ d)
    (v : Fin (k + 1) → Fin d → ℤ) (hv : AffineIndependent ℝ fun j => castVec (v j)) :
    ∃ (N : Fin (k + 1) → ℕ) (m : (j : Fin (k + 1)) → Fin (N j) → ℕ)
      (g : (j : Fin (k + 1)) → (i : Fin (N j)) → Fin (m j i) → Fin d → ℤ)
      (ε : (j : Fin (k + 1)) → Fin (N j) → ℤ),
      (∀ j i, IsPrimitiveGens (g j i)) ∧
      (∀ j, N j ≤ (2 ^ d) ^ iterCount d (coneIndex (edgeGens v j))) ∧
      (∀ j, IsSignedConeDecomp (supportingCone (simplex v) (castVec (v j))) (g j) (ε j)) ∧
      ∀ c : Fin d → ℝ, (∀ j i, IsRegular (g j i) c) →
        ∃ R : (j : Fin (k + 1)) → Fin (N j) → ℝ,
          (∀ j i, IsLaurentConstTerm
            (fun t => Real.exp (t * (c ⬝ᵥ castVec (v j))) * sigma (g j i) (t • c)) (R j i)) ∧
          (latticeCount (simplex v) : ℝ) = ∑ j, ∑ i, (ε j i : ℝ) * R j i := by
  classical
  choose L hlen hp hid hsig using fun j=>primitive_decomposition hd (edgeGens v j) (edgeGens_simple v hv j)
  refine ⟨fun j=>(L j).length,fun j i=>((L j).get i).dim,
    fun j i=>((L j).get i).gens,fun j i=>((L j).get i).coeff,?_,hlen,?_,?_⟩
  · intro j i
    exact hp j _ (List.get_mem _ _)
  · intro j x
    rw [supportingCone_simplex,hid j x,coneTermSum_indexed]
    rfl
  · intro c hc
    exact primitive_formula_constants v hv L (fun j q hq=>(hp j q hq).1) hsig c
      (fun j=>(listRegular_indexed_iff (L j) c).mpr (hc j))

end BarvinokCount.ShortFormula
-- End RootAssembly

-- Begin Solution

open BarvinokCount.ShortFormula

theorem solution {d k : ℕ} (hd : 2 ≤ d)
    (v : Fin (k + 1) → Fin d → ℤ) (hv : AffineIndependent ℝ fun j => castVec (v j)) :
    ∃ (N : Fin (k + 1) → ℕ) (m : (j : Fin (k + 1)) → Fin (N j) → ℕ)
      (g : (j : Fin (k + 1)) → (i : Fin (N j)) → Fin (m j i) → Fin d → ℤ)
      (ε : (j : Fin (k + 1)) → Fin (N j) → ℤ),
      (∀ j i, IsPrimitiveGens (g j i)) ∧
      (∀ j, N j ≤ (2 ^ d) ^ iterCount d (coneIndex (edgeGens v j))) ∧
      (∀ j, IsSignedConeDecomp (supportingCone (simplex v) (castVec (v j))) (g j) (ε j)) ∧
      ∀ c : Fin d → ℝ, (∀ j i, IsRegular (g j i) c) →
        ∃ R : (j : Fin (k + 1)) → Fin (N j) → ℝ,
          (∀ j i, IsLaurentConstTerm
            (fun t => Real.exp (t * (c ⬝ᵥ castVec (v j))) * sigma (g j i) (t • c)) (R j i)) ∧
          (latticeCount (simplex v) : ℝ) = ∑ j, ∑ i, (ε j i : ℝ) * R j i := by
  exact BarvinokCount.ShortFormula.latticeCount_eq_short_signed_sum hd v hv

-- End Solution
