-- Prove2me | solution 1 for CompanionTheory.HeckeA.coset_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:07.372599+00:00
-- url     : https://prove2.me/submissions/1f41255b-6002-4a95-9f88-4d1b33dfa31c

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Formalism.UG.P
noncomputable section
open CompanionTheory CompanionTheory.HeckeA
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)
open Classical
namespace CompanionTheory.HeckeA
theorem _root_.solution (J : Subgroup G) (hJ : ∀ h, ι h ∈ J ↔ h ∈ K) (d : H) {f : G → W} (hf : Inv ι K f) (g : G)
    {D : Set G} (hD : ∀ x, x ∈ D ↔ ∃ h ∈ DoubleCoset.doubleCoset d (K : Set H) K, ι h = x) :
    (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ D, (x : G ⧸ J) = c then f (g * hc.choose) else 0) = op ι K (dosetInd ℂ K d) f g := by
  have hmul : ∀ h ∈ DoubleCoset.doubleCoset d (K : Set H) K, ∀ k ∈ K,
      h * k ∈ DoubleCoset.doubleCoset d (K : Set H) K := fun h hh k hk => by
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * k, K.mul_mem hb hk, by group⟩
  have heq : ∀ h h' : H, ((ι h : G) : G ⧸ J) = (ι h' : G) ↔ h⁻¹ * h' ∈ K := fun h h' => by
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, hJ]
  have hinj : Function.Injective fun c : H ⧸ K => ((ι c.out : G) : G ⧸ J) := fun c c' h => by
    rw [← c.out_eq', ← c'.out_eq']
    exact QuotientGroup.eq.2 ((heq _ _).1 h)
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ _ (Set.range fun c : H ⧸ K => ((ι c.out : G) : G ⧸ J)),
    finsum_mem_range hinj]
  · refine finsum_congr fun c => ?_
    split_ifs with hc
    · obtain ⟨h, hh, e⟩ := (hD _).1 hc.choose_spec.1
      have e2 := hc.choose_spec.2
      rw [← e] at e2 ⊢
      have hk := (heq _ _).1 e2
      have e3 : c.out = h * (h⁻¹ * c.out) := by group
      rw [dosetInd, Set.indicator_of_mem (e3 ▸ hmul h hh _ hk), Pi.one_apply, one_smul, e3, map_mul, ← mul_assoc,
        hf _ _ hk]
    · rw [dosetInd, Set.indicator_of_notMem fun h => hc ⟨_, (hD _).2 ⟨_, h, rfl⟩, rfl⟩, zero_smul]
  · ext c
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, iff_and_self, Function.mem_support]
    intro hc
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ D, (x : G ⧸ J) = c := by
      by_contra h
      exact hc (dif_neg h)
    obtain ⟨h, -, rfl⟩ := (hD _).1 hx
    exact ⟨(h : H ⧸ K), (heq _ _).2 (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))⟩
end CompanionTheory.HeckeA
