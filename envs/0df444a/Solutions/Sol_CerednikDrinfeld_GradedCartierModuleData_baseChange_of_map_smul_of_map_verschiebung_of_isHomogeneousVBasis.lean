-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4c823d37-bc1e-5201-b0fc-a82db1f06b89

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis

set_option autoImplicit false

noncomputable section

namespace P2mBca

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {jR : Zp2 p →+* R}
  (E : GradedCartierModuleData p R jR)

theorem fin2_add_two (i : Fin 2) : i + 1 + 1 = i := by
  fin_cases i <;> rfl

theorem sum_two (i : Fin 2) (t : Fin 2 → E.M) : (∑ k : Fin 2, t k) = t i + t (i + 1) := by
  fin_cases i
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two, add_comm]

theorem sum_single (i : Fin 2) (a : R) (δ : Fin 2 → E.M) :
    (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single i a : Fin 2 → R) k) • δ k) =
      WittVector.teichmuller p a • δ i := by
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem piece_unique (i : Fin 2) {a a' b b' : E.M} (ha : a ∈ E.piece i) (ha' : a' ∈ E.piece (i + 1))
    (hb : b ∈ E.piece i) (hb' : b' ∈ E.piece (i + 1)) (h : a + a' = b + b') :
    a = b ∧ a' = b' := by
  have hdis : ∀ x : E.M, x ∈ E.piece i → x ∈ E.piece (i + 1) → x = 0 := by
    have d := Submodule.disjoint_def.1 E.isCompl_piece.disjoint
    fin_cases i
    · exact fun x h1 h2 => d x h1 h2
    · exact fun x h1 h2 => d x (by simpa using h2) h1
  have e : a - b = b' - a' := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h0 : a - b ∈ E.piece i := sub_mem ha hb
  have h1 : a - b ∈ E.piece (i + 1) := by rw [e]; exact sub_mem hb' ha'
  have hab : a = b := sub_eq_zero.1 (hdis _ h0 h1)
  refine ⟨hab, ?_⟩
  rw [hab] at h
  exact add_left_cancel h

theorem exists_piece_decomp (i : Fin 2) (y : E.M) :
    ∃ u u' : E.M, u ∈ E.piece i ∧ u' ∈ E.piece (i + 1) ∧ u + u' = y := by
  have c := Submodule.codisjoint_iff_exists_add_eq.1 E.isCompl_piece.codisjoint y
  fin_cases i
  · simpa using c
  · obtain ⟨u, u', hu, hu', e⟩ := c
    exact ⟨u', u, hu', by simpa using hu, by rw [add_comm]; exact e⟩

theorem diag1 (δ : Fin 2 → E.M) (hδ : E.IsHomogeneousVBasis δ) (i : Fin 2) (x : E.M) (hx : x ∈ E.piece i) :
    ∃ (a : R) (z : E.M), z ∈ E.piece (i + 1) ∧
      x = WittVector.teichmuller p a • δ i + E.verschiebung z := by
  obtain ⟨⟨c, y⟩, h, -⟩ := hδ.2 x
  change x = (∑ k : Fin 2, WittVector.teichmuller p (c k) • δ k) + E.verschiebung y at h
  obtain ⟨u, u', hu, hu', hy⟩ := exists_piece_decomp E i y
  rw [sum_two E i] at h
  have hA : x - WittVector.teichmuller p (c i) • δ i - E.verschiebung u' ∈ E.piece i := by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hδ.1 i))) ?_
    have := E.verschiebung_mem (i + 1) u' hu'
    rwa [fin2_add_two] at this
  have hB : WittVector.teichmuller p (c (i + 1)) • δ (i + 1) + E.verschiebung u ∈ E.piece (i + 1) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hδ.1 (i + 1))) (E.verschiebung_mem i u hu)
  have hAB : x - WittVector.teichmuller p (c i) • δ i - E.verschiebung u' =
      WittVector.teichmuller p (c (i + 1)) • δ (i + 1) + E.verschiebung u := by
    rw [h, ← hy, map_add]; abel
  have hB0 : WittVector.teichmuller p (c (i + 1)) • δ (i + 1) + E.verschiebung u = 0 := by
    have := piece_unique E i hA (Submodule.zero_mem _) (Submodule.zero_mem _) hB (by rw [hAB]; abel)
    exact this.2.symm
  have z1 : (0 : E.M) =
      (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single (i + 1) (c (i + 1)) : Fin 2 → R) k) • δ k) +
        E.verschiebung u := by
    rw [sum_single E]; exact hB0.symm
  have z2 : (0 : E.M) = (∑ k : Fin 2, WittVector.teichmuller p ((0 : Fin 2 → R) k) • δ k) +
      E.verschiebung 0 := by simp
  have hu0 := (hδ.2 0).unique (y₁ := ((Pi.single (i + 1) (c (i + 1)) : Fin 2 → R), u))
    (y₂ := (0, 0)) z1 z2
  have hc : c (i + 1) = 0 := by
    have := congrFun (congrArg Prod.fst hu0) (i + 1)
    simpa using this
  have hu00 : u = 0 := congrArg Prod.snd hu0
  refine ⟨c i, y, ?_, ?_⟩
  · rw [← hy, hu00, zero_add]; exact hu'
  · rw [h, hc]; simp

theorem iterV_zero (n : ℕ) : (⇑E.verschiebung)^[n] (0 : E.M) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

theorem iter_add (n : ℕ) (a b : E.M) :
    (⇑E.verschiebung)^[n] (a + b) = (⇑E.verschiebung)^[n] a + (⇑E.verschiebung)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

theorem eq_zero_of_forall_iterV (hc : E.IsVAdicallyComplete) (a : E.M)
    (h : ∀ N : ℕ, ∃ t : E.M, a = (⇑E.verschiebung)^[N] t) : a = 0 := by
  have hsum : ∀ N : ℕ, (∑ m ∈ Finset.range N, (⇑E.verschiebung)^[m] ((fun _ : ℕ => (0 : E.M)) m)) = 0 :=
    fun N => Finset.sum_eq_zero fun m _ => iterV_zero E m
  refine (hc (fun _ => (0 : E.M))).unique ?_ ?_
  · intro N
    obtain ⟨t, ht⟩ := h N
    exact ⟨t, by rw [hsum, zero_add]; exact ht⟩
  · intro N
    exact ⟨0, by rw [hsum, iterV_zero, add_zero]⟩

theorem iterV_two_mem (j : Fin 2) (N : ℕ) (x : E.M) (hx : x ∈ E.piece j) :
    (⇑E.verschiebung)^[2 * N] x ∈ E.piece j := by
  induction N with
  | zero => simpa using hx
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    have := E.verschiebung_mem _ _ (E.verschiebung_mem _ _ ih)
    rwa [fin2_add_two] at this

end P2mBca

end

open P2mBca in
theorem solution
    (p : ℕ) [Fact p.Prime] {T B' : Type} [CommRing T] [CommRing B']
    {jT : CerednikDrinfeld.Zp2 p →+* T} {j' : CerednikDrinfeld.Zp2 p →+* B'} (q : T →+* B')
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (h : DT.M →+ D'.M)
    (hsl : ∀ (w : WittVector p T) (x : DT.M), h (w • x) = WittVector.map q w • h x)
    (hV : ∀ x : DT.M, h (DT.verschiebung x) = D'.verschiebung (h x))
    (β : Fin 2 → DT.M) (hβ : DT.IsHomogeneousVBasis β) (hβ' : D'.IsHomogeneousVBasis (fun i => h (β i)))
    (hvarpi : ∀ i : Fin 2, h (DT.varpi (β i)) = D'.varpi (h (β i))) :
    CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DT D' h := by
  have hVinj : Function.Injective D'.verschiebung := hβ'.verschiebung_injective

  have hF : ∀ x : DT.M, h (DT.frobenius x) = D'.frobenius (h x) := by
    intro x
    apply hVinj
    rw [← hV, DT.verschiebung_frobenius, hsl, WittVector.map_verschiebung, map_one,
      D'.verschiebung_frobenius]

  have hPi : ∀ x : DT.M, h (DT.varpi x) = D'.varpi (h x) := by
    have key :=
      CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq
        p q DT D' hD' β hβ (h.comp DT.varpi.toAddMonoidHom) (D'.varpi.toAddMonoidHom.comp h)
        (fun w x => by simp [hsl])
        (fun x => by simp [DT.varpi_verschiebung, hV])
        (fun w x => by simp [hsl])
        (fun x => by simp [hV, D'.varpi_verschiebung])
        (fun i => by simpa using hvarpi i)
    intro x
    have := congrArg (fun F : DT.M →+ D'.M => F x) key
    simpa using this

  have descent : ∀ (N : ℕ) (i : Fin 2) (x : DT.M), x ∈ DT.piece i →
      ∃ a t : D'.M, a ∈ D'.piece i ∧ h x = a + (⇑D'.verschiebung)^[2 * N] t := by
    intro N
    induction N with
    | zero => intro i x _; exact ⟨0, h x, Submodule.zero_mem _, by simp⟩
    | succ N ih =>
      intro i x hx
      obtain ⟨a, z, hz, hxe⟩ := diag1 DT β hβ i x hx
      obtain ⟨b, z', hz', hze⟩ := diag1 DT β hβ (i + 1) z hz
      rw [fin2_add_two] at hz'
      obtain ⟨a'', t, ha'', hz'e⟩ := ih i z' hz'
      refine ⟨WittVector.teichmuller p (q a) • h (β i) +
          D'.verschiebung (WittVector.teichmuller p (q b) • h (β (i + 1)) + D'.verschiebung a''), t, ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hβ'.1 i)) ?_
        have hb1 : h (β (i + 1)) ∈ D'.piece (i + 1) := hβ'.1 (i + 1)
        have hin : WittVector.teichmuller p (q b) • h (β (i + 1)) + D'.verschiebung a'' ∈ D'.piece (i + 1) :=
          Submodule.add_mem _ (Submodule.smul_mem _ _ hb1) (D'.verschiebung_mem i _ ha'')
        have := D'.verschiebung_mem (i + 1) _ hin
        rwa [fin2_add_two] at this
      · rw [hxe, map_add, hsl, WittVector.map_teichmuller, hV, hze, map_add, hsl,
          WittVector.map_teichmuller, hV, hz'e, show 2 * (N + 1) = (2 * N + 1) + 1 by ring,
          Function.iterate_succ_apply', Function.iterate_succ_apply']
        simp only [map_add]
        abel
  have hpc : ∀ (i : Fin 2) (x : DT.M), x ∈ DT.piece i → h x ∈ D'.piece i := by
    intro i x hx
    obtain ⟨u, u', hu, hu', huu⟩ := exists_piece_decomp D' i (h x)
    have hu'0 : u' = 0 := by
      apply eq_zero_of_forall_iterV D' hD'.2
      intro N
      obtain ⟨a, t, ha, he⟩ := descent N i x hx
      obtain ⟨r, r', hr, hr', hrr⟩ := exists_piece_decomp D' i t
      have e : u + u' = (a + (⇑D'.verschiebung)^[2 * N] r) + (⇑D'.verschiebung)^[2 * N] r' := by
        rw [huu, he, ← hrr, iter_add]; abel
      have hu2 := piece_unique D' i hu hu' (Submodule.add_mem _ ha (iterV_two_mem D' i N r hr))
        (iterV_two_mem D' (i + 1) N r' hr') e
      refine ⟨(⇑D'.verschiebung)^[N] r', ?_⟩
      rw [hu2.2, two_mul, Function.iterate_add_apply]
    rw [← huu, hu'0, add_zero]; exact hu
  exact ⟨hsl, hF, hV, hPi, hpc, ⟨β, hβ, hβ'⟩⟩

end S_CerednikDrinfeld_GradedCartierModuleData_baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis (solution)
