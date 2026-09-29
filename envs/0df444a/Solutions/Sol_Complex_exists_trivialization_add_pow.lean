-- Prove2me | solution 1 for Complex.exists_trivialization_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/85d5e400-88b0-5adc-a497-dd81f1589410

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_trivialization_add_pow

set_option autoImplicit false

namespace PowTrivialization

open Complex

theorem mem_slitPlane_of_ray_avoid {b z : ℂ} {θ : ℝ}
    (hray : ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * I) ≠ z) :
    (z - b) * Complex.exp ((Real.pi - θ) * I) ∈ slitPlane := by
  set w := (z - b) * Complex.exp ((Real.pi - θ) * I) with hw
  by_contra hcon
  rw [mem_slitPlane_iff] at hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have hwre : w = (w.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using him
  have hw0 : (z - b) * Complex.exp ((↑Real.pi - ↑θ) * I) = (w.re : ℂ) := by
    rw [← hw]
    exact hwre
  have h4 : Complex.exp ((↑Real.pi - ↑θ) * I) * Complex.exp ((↑θ - ↑Real.pi) * I) = 1 := by
    rw [← Complex.exp_add,
      show ((↑Real.pi - ↑θ) * I + (↑θ - ↑Real.pi) * I : ℂ) = 0 by ring,
      Complex.exp_zero]
  have hkey : z - b = (w.re : ℂ) * Complex.exp ((↑θ - ↑Real.pi) * I) := by
    calc z - b
        = (z - b) * (Complex.exp ((↑Real.pi - ↑θ) * I)
            * Complex.exp ((↑θ - ↑Real.pi) * I)) := by rw [h4, mul_one]
    _ = (w.re : ℂ) * Complex.exp ((↑θ - ↑Real.pi) * I) := by rw [← mul_assoc, hw0]
  have hexp2 : Complex.exp ((↑θ - ↑Real.pi) * I) = -Complex.exp (↑θ * I) := by
    rw [show ((↑θ - ↑Real.pi) * I : ℂ) = ↑θ * I + -(↑Real.pi * I) by ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    field_simp
  refine hray (-w.re) (by linarith) ?_
  have hz : z = b + (w.re : ℂ) * -Complex.exp (↑θ * I) := by
    rw [← hexp2]
    linear_combination hkey
  rw [hz]
  push_cast
  ring

noncomputable def rootBranch (b : ℂ) (θ : ℝ) (e : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.log ((z - b) * Complex.exp ((Real.pi - θ) * I)) / e)
    * Complex.exp (((θ - Real.pi : ℝ)) * I / e)

theorem rootBranch_ne_zero (b : ℂ) (θ : ℝ) (e : ℕ) (z : ℂ) :
    rootBranch b θ e z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

theorem rootBranch_pow {b z : ℂ} {θ : ℝ} {e : ℕ} (he : e ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * I) ≠ z) :
    rootBranch b θ e z ^ e = z - b := by
  have hsp := mem_slitPlane_of_ray_avoid hray
  have hne : (z - b) * Complex.exp ((Real.pi - θ) * I) ≠ 0 :=
    slitPlane_ne_zero hsp
  have heC : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he
  rw [rootBranch, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    mul_div_cancel₀ _ heC, Complex.exp_log hne]
  have h2 : (e : ℂ) * (((θ - Real.pi : ℝ)) * I / e) = ((θ - Real.pi : ℝ)) * I := by
    field_simp
  rw [h2, mul_assoc, ← Complex.exp_add,
    show ((↑Real.pi - ↑θ) * I + ((θ - Real.pi : ℝ) : ℂ) * I : ℂ) = 0 by push_cast; ring,
    Complex.exp_zero, mul_one]

theorem continuousOn_rootBranch (b : ℂ) (θ : ℝ) (e : ℕ) {U : Set ℂ}
    (hray : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * I) ≠ z) :
    ContinuousOn (rootBranch b θ e) U := by
  refine ContinuousOn.mul ?_ continuousOn_const
  refine ContinuousOn.cexp ?_
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.clog ?_ ?_
  · fun_prop
  · intro z hz
    exact mem_slitPlane_of_ray_avoid (hray z hz)

section Assembly

theorem exists_evenlyCovered_data {b : ℂ} {θ : ℝ} {e : ℕ} (he : e ≠ 0)
    {U : Set ℂ}
    (hray : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * I) ≠ z) :
    ∃ H : ((fun ζ : ℂ => b + ζ ^ e) ⁻¹' U) ≃ₜ U × Fin e,
      ∀ ζ, ((H ζ).1 : ℂ) = b + (ζ : ℂ) ^ e := by
  classical
  haveI : NeZero e := ⟨he⟩
  set g : ℂ → ℂ := fun ζ => b + ζ ^ e with hg
  set σ : ℂ → ℂ := rootBranch b θ e with hσdef
  set ω : ℂ := Complex.exp (2 * Real.pi * I / e) with hω
  have hprim : IsPrimitiveRoot ω e := Complex.isPrimitiveRoot_exp e he
  have hωe : ω ^ e = 1 := hprim.pow_eq_one
  have hgU : ∀ ζ : g ⁻¹' U, g (ζ : ℂ) ∈ U := fun ζ => ζ.2
  have hσ_pow : ∀ z ∈ U, σ z ^ e = z - b := fun z hz => rootBranch_pow he (hray z hz)
  have hσ_ne : ∀ z : ℂ, σ z ≠ 0 := fun z => rootBranch_ne_zero b θ e z
  have hbU : b ∉ U := fun hbU => hray b hbU 0 le_rfl (by simp)
  have hgcont : Continuous g := by fun_prop
  have hσU : ContinuousOn σ U := continuousOn_rootBranch b θ e hray

  have hΦg : ∀ (z : U) (j : Fin e), g (ω ^ (j : ℕ) * σ (z : ℂ)) = (z : ℂ) := by
    intro z j
    show b + (ω ^ (j : ℕ) * σ (z : ℂ)) ^ e = (z : ℂ)
    rw [mul_pow, ← pow_mul, mul_comm (j : ℕ) e, pow_mul, hωe, one_pow, one_mul,
      hσ_pow _ z.2]
    ring
  have hΦmem : ∀ (z : U) (j : Fin e), ω ^ (j : ℕ) * σ (z : ℂ) ∈ g ⁻¹' U := by
    intro z j
    rw [Set.mem_preimage, hΦg z j]
    exact z.2

  have hroot : ∀ ζ : g ⁻¹' U, ((ζ : ℂ) / σ (g (ζ : ℂ))) ^ e = 1 := by
    intro ζ
    have hζ_pow : (ζ : ℂ) ^ e = g (ζ : ℂ) - b := by
      show (ζ : ℂ) ^ e = (b + (ζ : ℂ) ^ e) - b
      ring
    rw [div_pow, hσ_pow _ (hgU ζ), hζ_pow]
    refine div_self ?_
    intro h0
    exact hbU (sub_eq_zero.mp h0 ▸ hgU ζ)
  have hidx : ∀ ζ : g ⁻¹' U, ∃ i < e, ω ^ i = (ζ : ℂ) / σ (g (ζ : ℂ)) := fun ζ =>
    hprim.eq_pow_of_pow_eq_one (hroot ζ)
  set idx : g ⁻¹' U → Fin e := fun ζ =>
    ⟨(hidx ζ).choose, (hidx ζ).choose_spec.1⟩ with hidx_def
  have hidx_spec : ∀ ζ : g ⁻¹' U, (ζ : ℂ) = ω ^ ((idx ζ : Fin e) : ℕ) * σ (g (ζ : ℂ)) :=
    fun ζ => (div_eq_iff (hσ_ne _)).mp (hidx ζ).choose_spec.2.symm
  have hidx_unique : ∀ (ζ : g ⁻¹' U) (j : Fin e),
      (ζ : ℂ) = ω ^ (j : ℕ) * σ (g (ζ : ℂ)) → idx ζ = j := by
    intro ζ j hj
    have h1 : ω ^ (j : ℕ) * σ (g (ζ : ℂ)) = ω ^ ((idx ζ : Fin e) : ℕ) * σ (g (ζ : ℂ)) :=
      hj.symm.trans (hidx_spec ζ)
    have h2 : ω ^ (j : ℕ) = ω ^ ((idx ζ : Fin e) : ℕ) :=
      mul_right_cancel₀ (hσ_ne _) h1
    exact Fin.ext (hprim.pow_inj (idx ζ).2 j.2 h2.symm)

  let E : g ⁻¹' U ≃ U × Fin e :=
    { toFun := fun ζ => (⟨g (ζ : ℂ), hgU ζ⟩, idx ζ)
      invFun := fun p => ⟨ω ^ (p.2 : ℕ) * σ (p.1 : ℂ), hΦmem p.1 p.2⟩
      left_inv := fun ζ => Subtype.ext (hidx_spec ζ).symm
      right_inv := fun p => by
        have hfst : g (ω ^ (p.2 : ℕ) * σ (p.1 : ℂ)) = (p.1 : ℂ) := hΦg p.1 p.2
        refine Prod.ext (Subtype.ext hfst) ?_
        refine hidx_unique _ p.2 ?_
        show (ω ^ (p.2 : ℕ) * σ (p.1 : ℂ) : ℂ)
          = ω ^ (p.2 : ℕ) * σ (g (ω ^ (p.2 : ℕ) * σ (p.1 : ℂ)))
        rw [hfst] }

  set q : g ⁻¹' U → ℂ := fun ζ => (ζ : ℂ) / σ (g (ζ : ℂ)) with hq
  have hσg : Continuous fun ζ : g ⁻¹' U => σ (g (ζ : ℂ)) :=
    hσU.comp_continuous (hgcont.comp continuous_subtype_val) (fun ζ => hgU ζ)
  have hqcont : Continuous q :=
    continuous_subtype_val.div hσg (fun ζ => hσ_ne _)
  have hq_eq : ∀ ζ, q ζ = ω ^ ((idx ζ : Fin e) : ℕ) := by
    intro ζ
    show (ζ : ℂ) / σ (g (ζ : ℂ)) = ω ^ ((idx ζ : Fin e) : ℕ)
    rw [div_eq_iff (hσ_ne _)]
    exact hidx_spec ζ
  have hfib : ∀ j : Fin e,
      idx ⁻¹' {j} = q ⁻¹' ((Set.range fun k : Fin e => ω ^ (k : ℕ)) \ {ω ^ (j : ℕ)})ᶜ := by
    intro j
    ext ζ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_diff,
      Set.mem_range, not_and, not_not]
    constructor
    · intro hj hrange
      rw [hq_eq ζ, show idx ζ = j from hj]
    · intro himp
      have h1 : q ζ = ω ^ (j : ℕ) := himp ⟨idx ζ, (hq_eq ζ).symm⟩
      refine hidx_unique ζ j ?_
      rw [← h1]
      show (ζ : ℂ) = (ζ : ℂ) / σ (g (ζ : ℂ)) * σ (g (ζ : ℂ))
      rw [div_mul_cancel₀ _ (hσ_ne _)]
  have hidx_cont : Continuous idx := by
    rw [continuous_def]
    intro s _
    have hdecomp : idx ⁻¹' s = ⋃ j ∈ s, idx ⁻¹' {j} := by
      ext ζ
      simp
    rw [hdecomp]
    refine isOpen_biUnion fun j _ => ?_
    rw [hfib j]
    refine (IsClosed.preimage hqcont ?_).isOpen_compl
    exact ((Set.finite_range fun k : Fin e => ω ^ (k : ℕ)).subset Set.diff_subset).isClosed

  refine ⟨{ toEquiv := E
            continuous_toFun := ?_
            continuous_invFun := ?_ }, ?_⟩
  · refine Continuous.prodMk ?_ hidx_cont
    exact (hgcont.comp continuous_subtype_val).subtype_mk _
  · refine Continuous.subtype_mk ?_ _
    refine Continuous.mul ?_ ?_
    · exact (continuous_of_discreteTopology (α := Fin e)
        (f := fun j : Fin e => ω ^ (j : ℕ))).comp continuous_snd
    · exact hσU.comp_continuous (continuous_subtype_val.comp continuous_fst)
        (fun p => p.1.2)
  · intro ζ
    rfl

end Assembly

end PowTrivialization

theorem solution {b : ℂ} {θ : ℝ} {e : ℕ} (he : e ≠ 0) {U : Set ℂ}
    (hray : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * Complex.I) ≠ z) :
    ∃ H : ((fun ζ : ℂ => b + ζ ^ e) ⁻¹' U) ≃ₜ U × Fin e,
      ∀ ζ, ((H ζ).1 : ℂ) = b + (ζ : ℂ) ^ e := by
  exact PowTrivialization.exists_evenlyCovered_data (he := he) (hray := hray)

end S_Complex_exists_trivialization_add_pow
end P2MW
export P2MW.S_Complex_exists_trivialization_add_pow (solution)
