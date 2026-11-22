-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.span_character_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:43.788525+00:00
-- url     : https://prove2.me/submissions/a37faa28-527d-412d-8b5d-998a557a918c

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last


section
namespace Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
private lemma rep_eq {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (n : ℕ)
    (f f' : Fin n → V) (hli : LinearIndependent K (Sum.elim f f')) (p q p' q' : Fin n → K)
    (h : ∑ i, (p i • f i + q i • f' i) = ∑ i, (p' i • f i + q' i • f' i)) :
    ∀ i, p i = p' i ∧ q i = q' i := by
  have key := (Fintype.linearIndependent_iffₛ.mp hli) (Sum.elim p q) (Sum.elim p' q')
    (by simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using h)
  exact fun i => ⟨key (Sum.inl i), key (Sum.inr i)⟩
section unfold
variable {G X : Type} [Group G] [MulAction G X]
open MulAction
end unfold
section dualcap
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
end dualcap
section sametrace
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)
end sametrace
namespace Part2
end Part2
section dvrcard
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
end dvrcard
section count
variable {F : Type} [Field F] [Fintype F]
end count
section inert
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
end inert
section inert2
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end inert2
section inert3
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end inert3
section inert4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end inert4
section unram2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
end unram2
section orth
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
end orth
section unimod
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
end unimod
section unimod2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
end unimod2
section annih
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
end annih
section stdform
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end stdform
section hermjac
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
end hermjac
section hermjacA
variable {E : Type} [CommRing E]
end hermjacA
section hermjacA2
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
end hermjacA2
section hermjacB
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
end hermjacB
end Formalism.HermitianLatticeCounting.P.S4aux
namespace Formalism.HermitianLatticeCounting.P
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : SpanCharRing := by
  intro K V _ _ _ O θ hθ n f f' hli α α'
  set ti : K := ((θ⁻¹ : Kˣ) : K) with hti
  have hmi : (θ : K) * ti = 1 := by simp [hti]
  have hsmul : ∀ (o : O) (v : V), o • v = (o : K) • v := fun o v => rfl
  have hL : ti • (∑ i, α i • f i + ∑ i, α' i • f' i) =
      ∑ i, ((ti * α i) • f i + (ti * α' i) • f' i) := by
    rw [smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    simp only [smul_smul]
  have hM : ∀ b c : Fin n → K, ∑ i, b i • f i + ∑ i, c i • (ti • (f' i - f i)) =
      ∑ i, ((b i - ti * c i) • f i + (ti * c i) • f' i) := by
    intro b c
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    module
  rw [← Set.Sum.elim_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hsmul] at hc
    rw [hM, hL] at hc
    have hr := rep_eq n f f' hli _ _ _ _ hc
    intro i
    obtain ⟨h1, h2⟩ := hr i
    have hc2 : α' i = (c (Sum.inr i) : K) := by
      linear_combination (-(θ : K)) * h2 - (α' i - (c (Sum.inr i) : K)) * hmi
    refine ⟨hc2 ▸ (c (Sum.inr i)).2, (c (Sum.inl i) : K), (c (Sum.inl i)).2, ?_⟩
    rw [hc2]
    linear_combination (-(θ : K)) * h1 - (α i + (c (Sum.inr i) : K)) * hmi
  · intro h
    choose h1 x hx hxe using h
    refine ⟨Sum.elim (fun i => ⟨x i, hx i⟩) (fun i => ⟨α' i, h1 i⟩), ?_⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hsmul]
    rw [hM, hL]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    linear_combination (-ti) * hxe i - (x i) * hmi
end Formalism.HermitianLatticeCounting.P.S4aux
