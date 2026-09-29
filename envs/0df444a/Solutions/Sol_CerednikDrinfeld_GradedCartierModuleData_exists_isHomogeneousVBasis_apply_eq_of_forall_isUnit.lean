-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4beb458f-91ad-560c-9545-1cd2bccb8ae1

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit

set_option autoImplicit false

noncomputable section

namespace P2mVbp

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

theorem diag (γ δ : Fin 2 → E.M) (hγ : ∀ i, γ i ∈ E.piece i) (hδ : E.IsHomogeneousVBasis δ)
    (i : Fin 2) :
    ∃ (a : R) (z : E.M), z ∈ E.piece (i + 1) ∧
      γ i = WittVector.teichmuller p a • δ i + E.verschiebung z := by
  obtain ⟨⟨c, y⟩, h, -⟩ := hδ.2 (γ i)
  change γ i = (∑ k : Fin 2, WittVector.teichmuller p (c k) • δ k) + E.verschiebung y at h
  obtain ⟨u, u', hu, hu', hy⟩ := exists_piece_decomp E i y
  rw [sum_two E i] at h
  have hA : γ i - WittVector.teichmuller p (c i) • δ i - E.verschiebung u' ∈ E.piece i := by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (hγ i) (Submodule.smul_mem _ _ (hδ.1 i))) ?_
    have := E.verschiebung_mem (i + 1) u' hu'
    rwa [fin2_add_two] at this
  have hB : WittVector.teichmuller p (c (i + 1)) • δ (i + 1) + E.verschiebung u ∈ E.piece (i + 1) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hδ.1 (i + 1))) (E.verschiebung_mem i u hu)
  have hAB : γ i - WittVector.teichmuller p (c i) • δ i - E.verschiebung u' =
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

theorem unit_of_diag (γ δ : Fin 2 → E.M) (hδ : E.IsHomogeneousVBasis δ) (i : Fin 2) (a b : R)
    (z t : E.M) (h1 : γ i = WittVector.teichmuller p a • δ i + E.verschiebung z)
    (h2 : δ i = WittVector.teichmuller p b • γ i + E.verschiebung t) : b * a = 1 := by
  have e : WittVector.teichmuller p b • γ i + E.verschiebung t =
      WittVector.teichmuller p (b * a) • δ i +
        E.verschiebung (WittVector.frobenius (WittVector.teichmuller p b) • z + t) := by
    rw [h1, smul_add, smul_smul, ← map_mul, E.smul_verschiebung, map_add, add_assoc]
  have z1 : δ i = (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single i (b * a) : Fin 2 → R) k) • δ k) +
      E.verschiebung (WittVector.frobenius (WittVector.teichmuller p b) • z + t) := by
    rw [sum_single E]; exact h2.trans e
  have z2 : δ i = (∑ k : Fin 2, WittVector.teichmuller p ((Pi.single i (1 : R) : Fin 2 → R) k) • δ k) +
      E.verschiebung 0 := by
    rw [sum_single E]; simp
  have := congrFun (congrArg Prod.fst ((hδ.2 _).unique
    (y₁ := ((Pi.single i (b * a) : Fin 2 → R), _))
    (y₂ := ((Pi.single i (1 : R) : Fin 2 → R), (0 : E.M))) z1 z2)) i
  simpa using this

theorem recombine (c v : Fin 2 → R) (η w : Fin 2 → E.M) (y : E.M) :
    (∑ k : Fin 2, WittVector.teichmuller p (c k) •
        (WittVector.teichmuller p (v k) • η k + E.verschiebung (w k))) + E.verschiebung y =
      (∑ k : Fin 2, WittVector.teichmuller p (c k * v k) • η k) +
        E.verschiebung (y + ∑ k : Fin 2, WittVector.frobenius (WittVector.teichmuller p (c k)) • w k) := by
  simp only [Fin.sum_univ_two, smul_add, smul_smul, map_mul, E.smul_verschiebung, map_add]
  abel

theorem expand_exists {ε η : Fin 2 → E.M} (hε : E.IsHomogeneousVBasis ε) {v : Fin 2 → R}
    {w : Fin 2 → E.M} (K' : ∀ k, ε k = WittVector.teichmuller p (v k) • η k + E.verschiebung (w k))
    (x : E.M) :
    ∃ (c : Fin 2 → R) (y : E.M), x = (∑ k : Fin 2, WittVector.teichmuller p (c k) • η k) +
      E.verschiebung y := by
  obtain ⟨⟨c, y⟩, h, -⟩ := hε.2 x
  change x = (∑ k : Fin 2, WittVector.teichmuller p (c k) • ε k) + E.verschiebung y at h
  refine ⟨fun k => c k * v k, y + ∑ k : Fin 2, WittVector.frobenius (WittVector.teichmuller p (c k)) • w k, ?_⟩
  rw [h, show (∑ k : Fin 2, WittVector.teichmuller p (c k) • ε k) =
      ∑ k : Fin 2, WittVector.teichmuller p (c k) •
        (WittVector.teichmuller p (v k) • η k + E.verschiebung (w k)) from
    Finset.sum_congr rfl (fun k _ => by rw [K' k])]
  exact recombine E c v η w y

theorem expand_unique {ε η : Fin 2 → E.M} (hε : E.IsHomogeneousVBasis ε) {u v : Fin 2 → R}
    {w : Fin 2 → E.M} (K : ∀ k, η k = WittVector.teichmuller p (u k) • ε k + E.verschiebung (w k))
    (hvu : ∀ k, v k * u k = 1) (c : Fin 2 → R) (y : E.M) (c' : Fin 2 → R) (y' : E.M)
    (h : (∑ k : Fin 2, WittVector.teichmuller p (c k) • η k) + E.verschiebung y =
      (∑ k : Fin 2, WittVector.teichmuller p (c' k) • η k) + E.verschiebung y') :
    c = c' ∧ y = y' := by
  have H : ∀ (d : Fin 2 → R) (s : E.M),
      (∑ k : Fin 2, WittVector.teichmuller p (d k) • η k) + E.verschiebung s =
        (∑ k : Fin 2, WittVector.teichmuller p (d k * u k) • ε k) +
          E.verschiebung (s + ∑ k : Fin 2, WittVector.frobenius (WittVector.teichmuller p (d k)) • w k) := by
    intro d s
    rw [show (∑ k : Fin 2, WittVector.teichmuller p (d k) • η k) =
        ∑ k : Fin 2, WittVector.teichmuller p (d k) •
          (WittVector.teichmuller p (u k) • ε k + E.verschiebung (w k)) from
      Finset.sum_congr rfl (fun k _ => by rw [K k])]
    exact recombine E d u ε w s
  have hu0 := (hε.2 _).unique (y₁ := (fun k => c k * u k, _)) (y₂ := (fun k => c' k * u k, _))
    (H c y) (h.trans (H c' y'))
  have hcu : ∀ k, c k * u k = c' k * u k := fun k => congrFun (congrArg Prod.fst hu0) k
  have hc : c = c' := funext fun k => by
    have := congrArg (fun r => r * v k) (hcu k)
    simp only [mul_assoc, mul_comm (u k) (v k), hvu k, mul_one] at this
    exact this
  subst hc
  exact ⟨rfl, add_right_cancel (congrArg Prod.snd hu0)⟩

theorem iter_add (g : E.M →+ E.M) (n : ℕ) (a b : E.M) :
    (⇑g)^[n] (a + b) = (⇑g)^[n] a + (⇑g)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

section digits
variable {β : Fin 2 → E.M} (hβ : E.IsHomogeneousVBasis β)

def step (y : E.M) : (Fin 2 → R) × E.M := Classical.choose (hβ.2 y).exists

theorem step_spec (y : E.M) :
    y = (∑ k : Fin 2, WittVector.teichmuller p ((step E hβ y).1 k) • β k) +
      E.verschiebung (step E hβ y).2 :=
  Classical.choose_spec (hβ.2 y).exists

def rest (x : E.M) : ℕ → E.M
  | 0 => x
  | n + 1 => (step E hβ (rest x n)).2

def coef (x : E.M) (n : ℕ) : Fin 2 → R := (step E hβ (rest E hβ x n)).1

theorem rest_succ (x : E.M) (n : ℕ) :
    rest E hβ x n = (∑ k : Fin 2, WittVector.teichmuller p (coef E hβ x n k) • β k) +
      E.verschiebung (rest E hβ x (n + 1)) :=
  step_spec E hβ (rest E hβ x n)

theorem partial_sum (x : E.M) (N : ℕ) :
    x = (∑ m ∈ Finset.range N, (⇑E.verschiebung)^[m]
        (∑ k : Fin 2, WittVector.teichmuller p (coef E hβ x m k) • β k)) +
      (⇑E.verschiebung)^[N] (rest E hβ x N) := by
  induction N with
  | zero => simp [rest]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, Function.iterate_succ_apply, ← iter_add, ← rest_succ]
    exact ih

end digits

theorem semiconj_iterate {α γ : Type} (f : α → γ) (ga : α → α) (gb : γ → γ)
    (h : ∀ x, f (ga x) = gb (f x)) (n : ℕ) (x : α) : f (ga^[n] x) = gb^[n] (f x) :=
  Function.Semiconj.iterate_right (f := f) (ga := ga) (gb := gb) h n x

theorem surjective_of_baseChange {S B : Type} [CommRing S] [CommRing B]
    {jS : Zp2 p →+* S} {j : Zp2 p →+* B} (q : S →+* B) (hq : Function.Surjective q)
    (DS : GradedCartierModuleData p S jS) (hDSc : DS.IsVAdicallyComplete)
    (D : GradedCartierModuleData p B j) (hDc : D.IsVAdicallyComplete)
    (f : DS.M →+ D.M) (hfs : ∀ (w : WittVector p S) (x : DS.M), f (w • x) = WittVector.map q w • f x)
    (hfV : ∀ x, f (DS.verschiebung x) = D.verschiebung (f x))
    (γ0 : Fin 2 → DS.M) (hβ0 : D.IsHomogeneousVBasis (fun i => f (γ0 i))) :
    Function.Surjective f := by
  intro x
  obtain ⟨ℓ, hℓ⟩ := hq.hasRightInverse
  have hℓ' : ∀ b, q (ℓ b) = b := hℓ
  let xt : ℕ → DS.M := fun m =>
    ∑ k : Fin 2, WittVector.teichmuller p (ℓ (coef D hβ0 x m k)) • γ0 k
  have fxt : ∀ m, f (xt m) = ∑ k : Fin 2, WittVector.teichmuller p (coef D hβ0 x m k) • f (γ0 k) := by
    intro m
    simp only [xt, map_sum, hfs, WittVector.map_teichmuller, hℓ']
  obtain ⟨s, hs, -⟩ := hDSc xt
  refine ⟨s, ?_⟩
  apply (hDc (fun m => ∑ k : Fin 2, WittVector.teichmuller p (coef D hβ0 x m k) • f (γ0 k))).unique
  · intro N
    obtain ⟨t, ht⟩ := hs N
    refine ⟨f t, ?_⟩
    rw [ht, map_add, map_sum]
    simp only [semiconj_iterate f DS.verschiebung D.verschiebung hfV, fxt]
  · intro N
    exact ⟨rest D hβ0 x N, partial_sum D hβ0 x N⟩

end P2mVbp

end

open P2mVbp in
theorem solution
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B}
    (q : S →+* B) (hq : Function.Surjective q) (hu : ∀ s : S, IsUnit (q s) → IsUnit s)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (f : DS.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DS D f)
    (β : Fin 2 → D.M) (hβ : D.IsHomogeneousVBasis β) :
    ∃ γ : Fin 2 → DS.M, DS.IsHomogeneousVBasis γ ∧ ∀ i : Fin 2, f (γ i) = β i := by
  obtain ⟨γ0, hγ0, hβ0⟩ := hf.2.2.2.2.2
  have hfs := hf.1
  have hfV := hf.2.2.1
  have hfp := hf.2.2.2.2.1
  have hsurj : Function.Surjective f :=
    surjective_of_baseChange q hq DS hDS.2 D hD.2 f hfs hfV γ0 hβ0

  choose a z hz ha using fun i => diag D β (fun k => f (γ0 k)) hβ.1 hβ0 i
  choose b t ht hb using fun i => diag D (fun k => f (γ0 k)) β hβ0.1 hβ i
  have hba : ∀ i, b i * a i = 1 := fun i =>
    unit_of_diag D β (fun k => f (γ0 k)) hβ0 i (a i) (b i) (z i) (t i) (ha i) (hb i)

  choose aS haS using fun i => hq (a i)
  have hunit : ∀ i, IsUnit (aS i) := fun i =>
    hu _ (by rw [haS i]; exact IsUnit.of_mul_eq_one_right (b i) (hba i))
  choose v hvu using fun i => (hunit i).exists_left_inv

  choose zl hzl using fun i => hsurj (z i)
  have hzt : ∀ i, ∃ u : DS.M, u ∈ DS.piece (i + 1) ∧ f u = z i := by
    intro i
    obtain ⟨u, u', hu1, hu2, huu⟩ := exists_piece_decomp DS (i + 1) (zl i)
    refine ⟨u, hu1, ?_⟩
    have e : f u + f u' = z i + 0 := by rw [← map_add, huu, hzl i, add_zero]
    exact (piece_unique D (i + 1) (hfp _ _ hu1) (hfp _ _ hu2) (hz i)
      (Submodule.zero_mem _) e).1
  choose zt hztp hzt using hzt

  let γ : Fin 2 → DS.M := fun i => WittVector.teichmuller p (aS i) • γ0 i + DS.verschiebung (zt i)
  have K : ∀ k, γ k = WittVector.teichmuller p (aS k) • γ0 k + DS.verschiebung (zt k) := fun k => rfl
  have K' : ∀ k, γ0 k = WittVector.teichmuller p (v k) • γ k +
      DS.verschiebung (-(WittVector.frobenius (WittVector.teichmuller p (v k)) • zt k)) := by
    intro k
    have e : WittVector.teichmuller p (v k) • γ k =
        γ0 k + DS.verschiebung (WittVector.frobenius (WittVector.teichmuller p (v k)) • zt k) := by
      rw [K k, smul_add, smul_smul, ← map_mul, hvu k, map_one, one_smul, DS.smul_verschiebung]
    rw [map_neg, e]; abel
  refine ⟨γ, ⟨fun i => ?_, fun x => ?_⟩, fun i => ?_⟩
  ·
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ0.1 i)) ?_
    have := DS.verschiebung_mem (i + 1) (zt i) (hztp i)
    rwa [fin2_add_two] at this
  · obtain ⟨c, y, hx⟩ := expand_exists DS (ε := γ0) (η := γ) hγ0 K' x
    refine ⟨(c, y), hx, ?_⟩
    rintro ⟨c', y'⟩ hx'
    obtain ⟨hc, hy⟩ := expand_unique DS (ε := γ0) (η := γ) hγ0 K hvu c' y' c y (hx'.symm.trans hx)
    exact Prod.ext hc hy
  ·
    show f (WittVector.teichmuller p (aS i) • γ0 i + DS.verschiebung (zt i)) = β i
    rw [map_add, hfs, WittVector.map_teichmuller, haS i, hfV, hzt i]
    exact (ha i).symm

end S_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isHomogeneousVBasis_apply_eq_of_forall_isUnit (solution)
