-- Prove2me | solution 1 for Bl.FirstBlockLemmaH.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:03.834249+00:00
-- url     : https://prove2.me/submissions/d4debd02-9d15-4c99-9d15-d104fd45ca0c

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaH
namespace Bl.FirstBlockLemmaH
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} E V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V] {ι : Type} [Fintype.{0} ι] [DecidableEq.{1} ι]
  {b : Module.Basis.{0, 0, 0} ι E V} {M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V},
  Module.Finite.{0, 0} (NumberField.RingOfIntegers.{0} E) (Subtype.{1} fun (x : V) ↦ Membership.mem.{0, 0} M x) →
    Exists.{1} fun (s : NumberField.RingOfIntegers.{0} E) ↦
      And (Membership.mem.{0, 0} (nonZeroDivisors.{0} (NumberField.RingOfIntegers.{0} E)) s)
        (∀ (v : V),
          Membership.mem.{0, 0} M v →
            ∀ (i : ι),
              Membership.mem.{0, 0}
                (RingHom.range.{0, 0} (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} E) E))
                (HMul.hMul.{0, 0, 0}
                  (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} E) E) s)
                  (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Module.Basis.repr.{0, 0, 0} b) v) i))) := by
  intro E _ _ V _ _ _ _ ι _ _ b M hM
  obtain ⟨S, hS⟩ := Module.Finite.iff_fg.mp hM
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers E))
    (S ×ˢ (Finset.univ : Finset ι)) (fun p : V × ι => b.repr p.1 p.2)
  refine ⟨s, s.2, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    intro i
    have h := hs (x, i) (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hx, Finset.mem_univ _⟩)
    rw [IsLocalization.IsInteger, Algebra.smul_def] at h
    exact RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h)
  | zero =>
    intro i
    rw [map_zero, Finsupp.zero_apply, mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro i
    rw [map_add, Finsupp.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
    exact mul_mem (RingHom.mem_range_self _ a) (hx i)
end Bl.FirstBlockLemmaH
