-- Prove2me | solution 1 for Formalism.UG.P.gLoc_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:27.345166+00:00
-- url     : https://prove2.me/submissions/09b29b7c-da30-4ef6-ac28-7a445a4e27f3

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
import Theorems.Thm_Formalism_UG_P_gLoc_int_iff
import Theorems.Thm_Formalism_UG_P_gLoc_conj_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (e : A ≃+* L) (T : Subring A) (hT : ∀ x, x ∈ T ↔ e x ∈ intL L) (P : GL (Fin m) L)
    (hPO : P ∈ (bc (n := Fin m) (intL L).subtype).range) {σL : L →+* L}
    (H Lv : Subgroup (GL (Fin m) A))
    (hLv : ∀ g, g ∈ Lv ↔ g ∈ H ∧ g ∈ (bc (n := Fin m) T.subtype).range)
    (f : H ≃* GU σL m) (hf : ∀ x, ((f x : GU σL m) : GL (Fin m) L) = P⁻¹ * bc (e : A →+* L) x * P) :
    (Lv.subgroupOf H).map f.toMonoidHom = KU σL m := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨-, hxT⟩ := (hLv _).mp (Subgroup.mem_subgroupOf.mp hx)
    rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf]
    refine ⟨(f x).2, ?_⟩
    show ((f x : GU σL m) : GL (Fin m) L) ∈ _
    rw [hf]
    exact (gLoc_conj_mem _ P hPO _).mp ((gLoc_int_iff e T (intL L) hT _).mp hxT)
  · intro hy
    obtain ⟨x, rfl⟩ := f.surjective y
    refine ⟨x, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ((hLv _).mpr ⟨x.2, ?_⟩)
    rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf] at hy
    have h2 := hy.2
    change ((f x : GU σL m) : GL (Fin m) L) ∈ _ at h2
    rw [hf] at h2
    exact (gLoc_int_iff e T (intL L) hT _).mpr ((gLoc_conj_mem _ P hPO _).mpr h2)
end Formalism.UG.P
