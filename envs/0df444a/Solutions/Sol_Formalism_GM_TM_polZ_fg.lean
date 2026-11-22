-- Prove2me | solution 1 for Formalism.GM.TM.polZ_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:29.005574+00:00
-- url     : https://prove2.me/submissions/7a642e3d-c1f2-4bd2-9f7c-d81f07d84e62

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution {K r : ℕ} (LLw : Letters K) : (PolZ p r LLw).FG := by
  classical
  let bnd : Fin K × Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => LLw.total)
  let T : Finset (Fin K × Fin r →₀ ℕ) := Finset.Iic bnd
  have hfg : (Submodule.span ℤ_[p] ((fun m => (monomial m (1 : ℚ_[p]) : MvPolynomial (Fin K × Fin r) ℚ_[p])) ''
      (T : Set (Fin K × Fin r →₀ ℕ)))).FG := Submodule.fg_span ((T.finite_toSet).image _)
  refine Submodule.FG.of_le hfg ?_
  intro x hx
  have hxP : x ∈ Pol p r LLw := (Submodule.mem_inf.mp hx).1
  have hxI := (Submodule.mem_inf.mp hx).2
  rw [Pol, mem_restrictSupport_iff] at hxP
  obtain ⟨y, hy⟩ := hxI
  rw [x.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmT : m ∈ T := by
    rw [Finset.mem_Iic, Finsupp.le_def]
    intro a
    have hmd : MultiDeg LLw m := hxP (Finset.mem_coe.mpr hm)
    have h1 : m a ≤ ∑ c, m (a.1, c) :=
      Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)
    have h2 : LLw.deg a.1 ≤ LLw.total :=
      Finset.single_le_sum (f := fun i => LLw.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)
    have h3 : bnd a = LLw.total := by simp [bnd]
    rw [h3]
    rw [hmd a.1] at h1
    omega
  have hco : x.coeff m = algebraMap ℤ_[p] ℚ_[p] (y.coeff m) := by
    rw [← hy]
    simp [MvPolynomial.coeff_map]
  have : monomial m (x.coeff m) = y.coeff m • (monomial m (1 : ℚ_[p])) := by
    rw [hco, MvPolynomial.smul_monomial, Algebra.smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, Finset.mem_coe.mpr hmT, rfl⟩)
end Formalism.GM.TM
