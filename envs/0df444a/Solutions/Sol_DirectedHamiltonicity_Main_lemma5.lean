-- Prove2me | solution 1 for DirectedHamiltonicity.Main.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T06:49:27.39701+00:00
-- url     : https://prove2.me/submissions/f9496039-5228-4b5e-b584-8b1bdd42de87

import Theorems.Thm_DirectedHamiltonicity_Main_lemma6

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph MvPolynomial Classical
open scoped BigOperators

namespace DHCArcSampling

private abbrev Labels (d : ℕ) := Finset (Fin d)
private noncomputable def rho (d : ℕ) : ℝ := (1 - delta d) / ((2 : ℝ)^d - 1)

private theorem weights {d : ℕ} (hd : 2 ≤ d) :
    0 ≤ delta d ∧ delta d ≤ rho d ∧ 3 * rho d ≤ 1 ∧
      (delta d)^2 + (rho d)^2 = delta d ∧ delta d ≤ 1 := by
  let k : ℝ := 2^d-1
  have hk : 3 ≤ k := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hd
    norm_num at h
    dsimp [k]; linarith
  have hk0 : 0 < k := by linarith
  have hpos : 0 < 1+k^2 := by positivity
  have hδ : delta d = 1/(1+k^2) := rfl
  have hρ : rho d = k/(1+k^2) := by
    change (1-1/(1+k^2))/k = _
    field_simp
    ring
  rw [hδ,hρ]
  refine ⟨by positivity, (div_le_div_iff_of_pos_right hpos).2 (by linarith), ?_, ?_, ?_⟩
  · rw [← mul_div_assoc, div_le_one hpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hk0.le]
  · field_simp
  · rw [div_le_one hpos]; nlinarith [sq_nonneg k]

private theorem weight_range {d : ℕ} (hd : 2 ≤ d) (l : Labels d) :
    0 ≤ copySetProb d l ∧ copySetProb d l ≤ rho d := by
  have h := weights hd
  unfold copySetProb
  change 0 ≤ (if l = ∅ then delta d else rho d) ∧ _
  split_ifs
  · exact ⟨h.1,h.2.1⟩
  · exact ⟨h.1.trans h.2.1,le_rfl⟩

private theorem normalized {d : ℕ} (hd : 2 ≤ d) : (∑ l : Labels d, copySetProb d l) = 1 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Labels d))]
  have hn : (Finset.univ.erase (∅ : Labels d)).card = 2^d-1 := by simp [Labels]
  have he : ∀ l ∈ Finset.univ.erase (∅ : Labels d), copySetProb d l = rho d :=
    fun l hl => if_neg (Finset.ne_of_mem_erase hl)
  rw [Finset.sum_congr rfl he,Finset.sum_const,hn,nsmul_eq_mul]
  have hp : (1:ℕ) < 2^d := Nat.one_lt_pow (by omega) (by decide)
  rw [Nat.cast_sub hp.le,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rw [show copySetProb d (∅ : Labels d) = delta d from if_pos rfl]
  unfold rho
  have hpos : 0 < (2:ℝ)^d - 1 := sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  field_simp [ne_of_gt hpos]
  ring

/-- Sum a product law over one coordinate at a time, starting from a successful
deterministic assignment. -/
private theorem expose {n : ℕ} (B : Fin n → Type) [∀ j, Fintype (B j)]
    (μ : ∀ j, B j → ℝ) (hμ : ∀ j b, 0 ≤ μ j b) (c : ℝ) (hc : 0 ≤ c)
    (Good : (∀ j, B j) → Prop) (base : ∀ j, B j) (seed : Good base)
    (row : ∀ v, Good v → ∀ j, c ≤ ∑ b, if Good (Function.update v j b) then μ j b else 0) :
    c^n ≤ ∑ v, if Good v then ∏ j, μ j (v j) else 0 := by
  classical
  induction n with
  | zero =>
    have hall (v : ∀ j, B j) : Good v := Subsingleton.elim base v ▸ seed
    simp [hall]
  | succ n ih =>
    let G (v : ∀ j : Fin n, B j.succ) := Good (Fin.cons (base 0) v)
    have tail := ih (fun j => B j.succ) (fun j => μ j.succ) (fun j => hμ j.succ)
      G (Fin.tail base) (by simpa [G] using seed) (by
        intro v hv j
        simpa [G] using row (Fin.cons (base 0) v) hv j.succ)
    have split : (∑ v, if Good v then ∏ j, μ j (v j) else 0) =
        ∑ v : ∀ j : Fin n, B j.succ, (∏ j, μ j.succ (v j)) *
          ∑ a : B 0, if Good (Fin.cons a v) then μ 0 a else 0 := by
      rw [← (Fin.consEquiv B).sum_comp (fun v => if Good v then ∏ j, μ j (v j) else 0),
        Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      change (if Good (Fin.cons a v) then ∏ j, μ j (Fin.cons a v j) else 0) = _
      by_cases good : Good (Fin.cons a v) <;> simp [good,Fin.prod_univ_succ,mul_comm]
    rw [split,pow_succ]
    apply (mul_le_mul_of_nonneg_right tail hc).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro v _
    have nonneg : 0 ≤ ∏ j, μ j.succ (v j) := Finset.prod_nonneg fun j _ => hμ _ _
    by_cases hv : G v
    · rw [if_pos hv]
      apply mul_le_mul_of_nonneg_left _ nonneg
      simpa using row (Fin.cons (base 0) v) hv 0
    · rw [if_neg hv, zero_mul]
      apply mul_nonneg nonneg
      exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hμ]

private noncomputable def label {d : ℕ} {σ : Type} (z : Fin d → σ) (l : Labels d) :
    MvPolynomial σ (ZMod 2) := ∑ k ∈ l, X (z k)

/-- Lemma 6 bounds the number of cancelling bit matrices. The zero matrix has
mass δ^p, and each remaining matrix has mass at most ρ^p. -/
private theorem cancel_mass {d p : ℕ} {σ : Type} (hd : 2 ≤ d) (hp : 1 ≤ p)
    (z : Fin p × Fin d → σ) (hz : Function.Injective z)
    (f : Fin p → MvPolynomial σ (ZMod 2)) (hf : ∀ i, f i ≠ 0) :
    (∑ S ∈ Finset.univ.filter (fun S : Fin p → Labels d =>
        ∑ i, label (fun k => z (i,k)) (S i) * f i = 0),
      ∏ i, copySetProb d (S i)) ≤ delta d := by
  classical
  let Bad (S : Fin p → Labels d) := (∑ i, label (fun k => z (i,k)) (S i) * f i) = 0
  let U := Finset.univ.filter Bad
  let bit (S : Fin p → Labels d) (j : Fin p × Fin d) : ZMod 2 := if j.2 ∈ S j.1 then 1 else 0
  have mem (S) (hS : Bad S) : bit S ∈ cancelSpace z f := by
    apply LinearMap.mem_ker.mpr
    simp only [LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply,
      Fintype.sum_prod_type,smul_eq_C_mul]
    unfold Bad label at hS
    rw [← hS]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    have eq : (∑ k ∈ S i, X (z (i,k)) * f i) =
        ∑ k : Fin d, if k ∈ S i then X (z (i,k)) * f i else 0 := by
      rw [← Finset.sum_filter]; simp
    rw [eq]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ S i <;> simp [bit,hk]
  let code (S : U) : cancelSpace z f := ⟨bit S.1,mem _ (Finset.mem_filter.mp S.2).2⟩
  have inj : Function.Injective code := by
    intro A B h
    apply Subtype.ext
    funext i
    ext l
    have hb := congrFun (congrArg Subtype.val h) (i,l)
    change bit A.1 (i,l) = bit B.1 (i,l) at hb
    by_cases ha : l ∈ A.1 i <;> by_cases hb' : l ∈ B.1 i <;> simp_all [bit]
  have dim := (DirectedHamiltonicity.Main.lemma6 (ZMod 2) σ p d hp (by omega) z hz f hf).2
    (by simp)
  have card : U.card ≤ 2^(p-1) := by
    have hinj := Nat.card_le_card_of_injective code inj
    exact (by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hinj :
      U.card ≤ Nat.card (cancelSpace z f)) |>.trans dim
  let O : Fin p → Labels d := fun _ => ∅
  have hO : O ∈ U := by simp [U,Bad,O,label]
  change ∑ S ∈ U, (∏ i, copySetProb d (S i)) ≤ delta d
  rw [← Finset.sum_erase_add _ _ hO]
  have h0 : (∏ i, copySetProb d (O i)) = (delta d)^p := by simp [O,copySetProb]
  rw [h0]
  have hμ := weights hd
  have hδ0 := hμ.1
  have hρ0 := hδ0.trans hμ.2.1
  have hmax := hμ.2.2.1
  have hδ1 := hμ.2.2.2.2
  have each (S : Fin p → Labels d) : (∏ i, copySetProb d (S i)) ≤ (rho d)^p := by
    simpa using Finset.prod_le_prod (s := Finset.univ) (fun i _ => (weight_range hd (S i)).1)
      (fun i _ => (weight_range hd (S i)).2)
  have bound : (∑ S ∈ U.erase O, ∏ i, copySetProb d (S i)) ≤
      ((2^(p-1)-1 : ℕ) : ℝ) * (rho d)^p := by
    apply (Finset.sum_le_sum (fun S _ => each S)).trans
    rw [Finset.sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ0 _)
    exact_mod_cast (Finset.card_erase_of_mem hO ▸ Nat.sub_le_sub_right card 1)
  apply (add_le_add_left bound _).trans
  rcases p with _ | p
  · omega
  cases p with
  | zero => simp
  | succ n =>
    have rad (k : ℕ) : ((2^(k+1)-1 : ℕ) : ℝ) * (rho d)^(k+2) ≤ (rho d)^2 := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hpow : 2 ≤ (2:ℕ)^(k+1) := by
          exact Nat.le_of_dvd (by positivity) (dvd_pow_self 2 (by omega))
        have hcoef : 2^(k+2)-1 ≤ 3*(2^(k+1)-1) := by rw [pow_succ (2:ℕ) (k+1)]; omega
        have hcoe : ((2^(k+2)-1 : ℕ) : ℝ) ≤ 3 * ((2^(k+1)-1 : ℕ) : ℝ) := by exact_mod_cast hcoef
        calc
          _ ≤ (3*((2^(k+1)-1 : ℕ):ℝ)) * (rho d)^(k+3) := mul_le_mul_of_nonneg_right hcoe (pow_nonneg hρ0 _)
          _ = (((2^(k+1)-1 : ℕ):ℝ) * (rho d)^(k+2)) * (3*rho d) := by rw [pow_succ (rho d) (k+2)]; ring
          _ ≤ (((2^(k+1)-1 : ℕ):ℝ) * (rho d)^(k+2)) * 1 :=
            mul_le_mul_of_nonneg_left hmax (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ0 _))
          _ ≤ _ := by simpa using ih
    have dec : (delta d)^(n+2) ≤ (delta d)^2 :=
      pow_le_pow_of_le_one hδ0 hδ1 (by omega)
    exact (add_le_add (rad n) dec).trans (by linarith [hμ.2.2.2.1])

private theorem total {d : ℕ} (hd : 2 ≤ d) (I : Type) [Fintype I] :
    (∑ S : I → Labels d, ∏ i, copySetProb d (S i)) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [normalized hd]

private noncomputable def linear {I σ : Type} [Fintype I] {d : ℕ} (z : I × Fin d → σ)
    (f : I → MvPolynomial σ (ZMod 2)) (S : I → Labels d) := ∑ i, label (fun k => z (i,k)) (S i) * f i

private theorem all_active {d : ℕ} {I σ : Type} [Fintype I] [Nonempty I] (hd : 2 ≤ d)
    (z : I × Fin d → σ) (hz : Function.Injective z) (f : I → MvPolynomial σ (ZMod 2))
    (hf : ∀ i, f i ≠ 0) :
    1 - delta d ≤ ∑ S : I → Labels d, if linear z f S ≠ 0 then ∏ i, copySetProb d (S i) else 0 := by
  classical
  let e := (Fintype.equivFin I).symm
  let z' (j : Fin (Fintype.card I) × Fin d) := z (e j.1,j.2)
  have hz' : Function.Injective z' := by
    intro a b h
    have eq := hz h
    exact Prod.ext (e.injective (congrArg Prod.fst eq)) (congrArg (fun x : I × Fin d => x.2) eq)
  have bound := cancel_mass hd Fintype.card_pos z' hz' (f ∘ e) (fun i => hf _)
  rw [Finset.sum_filter] at bound
  let M (S : I → Labels d) := ∏ i, copySetProb d (S i)
  have cancel : (∑ S, if linear z f S = 0 then M S else 0) ≤ delta d := by
    apply le_trans (le_of_eq ?_) bound
    let re := Equiv.arrowCongr e.symm (Equiv.refl (Labels d))
    apply Fintype.sum_equiv re
    intro S
    have he (j) : re S j = S (e j) := rfl
    have hlin : linear z f S = ∑ j, label (fun k => z' (j,k)) (re S j) * (f ∘ e) j := by
      exact (e.sum_comp (fun i => label (fun k => z (i,k)) (S i) * f i)).symm
    rw [hlin]
    split_ifs
    · exact (e.prod_comp (fun i => copySetProb d (S i))).symm
    · rfl
  have split : (∑ S, if linear z f S = 0 then M S else 0) +
      (∑ S, if linear z f S ≠ 0 then M S else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← total hd I]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h : linear z f S = 0 <;> simp [M,h]
  change 1 - delta d ≤ ∑ S, if linear z f S ≠ 0 then M S else 0
  linarith

/-- Integrate out arcs with zero coefficient before applying the cancellation bound. -/
private theorem one_row {d : ℕ} {I σ : Type} [Fintype I] (hd : 2 ≤ d)
    (z : I × Fin d → σ) (hz : Function.Injective z) (f : I → MvPolynomial σ (ZMod 2))
    (hf : ∃ i, f i ≠ 0) :
    1 - delta d ≤ ∑ S : I → Labels d, if linear z f S ≠ 0 then ∏ i, copySetProb d (S i) else 0 := by
  classical
  let P i := f i ≠ 0
  let J := {i // P i}
  let N := {i // ¬P i}
  let _ : DecidableEq J := Classical.typeDecidableEq J
  let _ : DecidableEq N := Classical.typeDecidableEq N
  let z' (j : J × Fin d) := z (j.1.1,j.2)
  let f' (i : J) := f i.1
  obtain ⟨j,hj⟩ := hf
  have : Nonempty J := ⟨⟨j,hj⟩⟩
  have hz' : Function.Injective z' := by
    intro a b h
    have eq := hz h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst eq)) (congrArg (fun x : I × Fin d => x.2) eq)
  apply (all_active hd z' hz' f' (fun i => i.2)).trans
  apply le_of_eq
  symm
  let re := Equiv.piEquivPiSubtypeProd P (fun _ => Labels d)
  let val (a : J → Labels d) := if linear z' f' a ≠ 0 then ∏ j, copySetProb d (a j) else 0
  have hlin (S : I → Labels d) : linear z f S = linear z' f' (re S).1 := by
    unfold linear
    rw [← Fintype.sum_subtype_add_sum_subtype P]
    have hz0 (i : N) : f i.1 = 0 := not_ne_iff.mp i.2
    simp [hz0,f',z',re,J,N]
  calc
    _ = ∑ x : (J → Labels d) × (N → Labels d), val x.1 * ∏ i, copySetProb d (x.2 i) := by
      apply Fintype.sum_equiv re
      intro S
      rw [hlin]
      unfold val
      split_ifs
      · exact (Fintype.prod_subtype_mul_prod_subtype P (fun i => copySetProb d (S i))).symm
      · simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr (by ext; simp)
      intro a _
      change (∑ b : N → Labels d, val a * ∏ i, copySetProb d (b i)) = val a
      rw [← Finset.mul_sum]
      refine (congrArg (val a * ·) ?_).trans (mul_one (val a))
      refine Eq.trans ?_ (total hd N)
      apply Finset.sum_congr (by ext; simp)
      intro b _
      rfl

variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
variable (s t : V) (hs : ∀ u, ¬adj u s) (ht : ∀ v, ¬adj t v)
private abbrev Pos (V : Type) [Fintype V] := Fin (Fintype.card V-1)
private abbrev NT (t : V) := {v : V // v ≠ t}
private abbrev NS (s : V) := {v : V // v ≠ s}
private abbrev Path := ↥((ofAdj adj).hamPaths s t)
private def src (a : SArc adj) : NT t := ⟨a.1.1,fun h => ht a.1.2 (h ▸ a.2)⟩
private def dst (a : SArc adj) : NS s := ⟨a.1.2,fun h => hs a.1.1 (h ▸ a.2)⟩
private abbrev J (t : V) := Fin (Fintype.card (NT t))
private noncomputable def idx (a : SArc adj) : J t := Fintype.equivFin (NT t) (src adj t ht a)
private abbrev Row (j : J t) := {a : SArc adj // idx adj t ht a = j}
private abbrev Pol (s : V) (d : ℕ) := MvPolynomial (NS s × Fin d) (ZMod 2)

omit [DecidableEq V] in
private theorem tail_injective (P : Path adj s t) :
    Function.Injective (fun i => (P.1 i).1.1) := by
  have hp : (ofAdj adj).IsHamPath s t P.1 := (Finset.mem_filter.mp P.2).2
  intro i j hij
  apply Fin.castSucc_injective
  exact hp.2.1 ((hp.1 i).symm.trans (hij.trans (hp.1 j)))

private noncomputable def slots (P : Path adj s t) : Pos V ≃ J t := by
  apply Equiv.ofBijective (fun i => idx adj t ht (P.1 i))
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j he
    exact tail_injective adj s t P (congrArg Subtype.val ((Fintype.equivFin (NT t)).injective he))
  · simp [J,NT,Fintype.card_subtype_compl]

private noncomputable def form {d : ℕ} (S : SArc adj → Labels d) (a : SArc adj) : Pol s d :=
  label (fun l => (dst adj s hs a,l)) (S a)

include hs in
private theorem poly_sum {d : ℕ} (S : SArc adj → Labels d) :
    pathPoly adj s t S = ∑ P : Path adj s t, ∏ i, form adj s hs S (P.1 i) := by
  classical
  unfold pathPoly
  rw [Finset.univ_eq_attach, Finset.sum_attach ((ofAdj adj).hamPaths s t) (fun P : Pos V → SArc adj => ∏ i, form adj s hs S (P i))]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  have h : (P i).1.2 ≠ s := (dst adj s hs (P i)).2
  simp [h,dst]

omit [DecidableEq V] in
/-- A path whose every arc belongs to a fixed Hamiltonian path must follow it
at each position, since each tail on that path has a unique successor arc. -/
private theorem forced (P Q : Path adj s t) (uses : ∀ i, ∃ j, Q.1 i = P.1 j) : Q = P := by
  have hp : (ofAdj adj).IsHamPath s t P.1 := (Finset.mem_filter.mp P.2).2
  have hq : (ofAdj adj).IsHamPath s t Q.1 := (Finset.mem_filter.mp Q.2).2
  have step (i) (h : (ofAdj adj).walkVerts s Q.1 i.castSucc = (ofAdj adj).walkVerts s P.1 i.castSucc) :
      Q.1 i = P.1 i := by
    obtain ⟨j,hj⟩ := uses i
    have hj' := tail_injective adj s t P
      ((congrArg (fun a : SArc adj => a.1.1) hj).symm.trans ((hq.1 i).trans (h.trans (hp.1 i).symm)))
    exact hj'.symm ▸ hj
  have v (j) : (ofAdj adj).walkVerts s Q.1 j = (ofAdj adj).walkVerts s P.1 j := by
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih => simpa [walkVerts,ofAdj] using congrArg (fun a : SArc adj => a.1.2) (step i ih)
  exact Subtype.ext (funext fun i => step i (v i.castSucc))

include hs in
private theorem seed_graph {d : ℕ} (hd : 2 ≤ d) (P : Path adj s t) :
    ∃ S : SArc adj → Labels d, pathPoly adj s t S ≠ 0 := by
  classical
  let l : Fin d := ⟨0,by omega⟩
  let S (a : SArc adj) : Labels d := if ∃ i, a = P.1 i then {l} else ∅
  refine ⟨S,?_⟩
  rw [poly_sum adj s t hs,Finset.sum_eq_single P]
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have h : ∃ j, P.1 i = P.1 j := ⟨i,rfl⟩
    simp [form,label,S,h]
  · intro Q _ hQP
    obtain ⟨i,hi⟩ : ∃ i, ¬∃ j, Q.1 i = P.1 j := by
      by_contra! hall
      exact hQP (forced adj s t P Q hall)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [form,label,S,hi])
  · simp

private noncomputable def splitRows {d : ℕ} :
    (SArc adj → Labels d) ≃ ((j : J t) → Row adj t ht j → Labels d) where
  toFun S _ a := S a.1
  invFun Y a := Y (idx adj t ht a) ⟨a,rfl⟩
  left_inv _ := rfl
  right_inv Y := by
    funext j a
    obtain ⟨e,h⟩ := a
    subst j
    rfl

include hs in
set_option maxHeartbeats 1200000 in
/-- Holding all other tails fixed, each path contributes exactly one factor
from the chosen tail. Its possible heads give distinct blocks of variables. -/
private theorem row_step {d : ℕ} (hd : 2 ≤ d)
    (Y : (j : J t) → Row adj t ht j → Labels d)
    (hY : pathPoly adj s t ((splitRows adj t ht).symm Y) ≠ 0) (j : J t) :
    1-delta d ≤ ∑ L : Row adj t ht j → Labels d,
      if pathPoly adj s t ((splitRows adj t ht).symm (Function.update Y j L)) ≠ 0
      then ∏ a, copySetProb d (L a) else 0 := by
  classical
  let B := Row adj t ht j
  let z (b : B × Fin d) := (dst adj s hs b.1.1,b.2)
  have hz : Function.Injective z := by
    intro b c he
    refine Prod.ext ?_ (congrArg (fun x : NS s × Fin d => x.2) he)
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext ?_ (congrArg (fun x : NS s × Fin d => x.1.1) he)
    exact congrArg Subtype.val ((Fintype.equivFin (NT t)).injective (b.1.2.trans c.1.2.symm))
  let pos (P : Path adj s t) := (slots adj s t ht P).symm j
  have index (P : Path adj s t) : idx adj t ht (P.1 (pos P)) = j := (slots adj s t ht P).apply_symm_apply j
  let arc (P : Path adj s t) : B := ⟨P.1 (pos P),index P⟩
  let rest (P : Path adj s t) := ∏ i ∈ Finset.univ.erase (pos P),
    form adj s hs ((splitRows adj t ht).symm Y) (P.1 i)
  let f (a : B) : Pol s d := ∑ P : Path adj s t, if arc P = a then rest P else 0
  let after (L : B → Labels d) := (splitRows adj t ht).symm (Function.update Y j L)
  have within (L) (a : B) : after L a.1 = L a := by
    obtain ⟨e,h⟩ := a
    change (Function.update Y j L) (idx adj t ht e) ⟨e,rfl⟩ = _
    subst j
    simp
  have outside (L) (e : SArc adj) (h : idx adj t ht e ≠ j) :
      after L e = (splitRows adj t ht).symm Y e := by
    change (Function.update Y j L) (idx adj t ht e) ⟨e,rfl⟩ = _
    rw [Function.update_of_ne h]
    rfl
  have expansion (L : B → Labels d) : pathPoly adj s t (after L) = linear z f L := by
    rw [poly_sum adj s t hs]
    unfold linear f
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro P _
    rw [Finset.sum_eq_single (arc P)]
    · simp only [if_true]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (pos P))]
      congr 1
      · change label _ (after L (arc P).1) = _
        rw [within]
      · apply Finset.prod_congr rfl
        intro i hi
        have hj : idx adj t ht (P.1 i) ≠ j := fun he =>
          (Finset.ne_of_mem_erase hi) ((slots adj s t ht P).injective (he.trans (index P).symm))
        change label _ (after L (P.1 i)) = _
        rw [outside L _ hj]
        rfl
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  have active : ∃ a, f a ≠ 0 := by
    by_contra! hz0
    apply hY
    have h := expansion (Y j)
    simpa [after,linear,hz0] using h
  have h := one_row hd z hz f active
  refine h.trans (le_of_eq ?_)
  apply Finset.sum_congr (by ext; simp)
  intro L _
  rw [← expansion]
  dsimp only [after]
  split_ifs <;> rfl

include hs ht in
set_option maxHeartbeats 1200000 in
private theorem success (d : ℕ) (hd : 2 ≤ d) (P : Path adj s t) :
    (1-delta d)^(Fintype.card V - 1) ≤ copyProb (adj := adj) d (fun S => pathPoly adj s t S ≠ 0) := by
  classical
  let B (j : J t) := Row adj t ht j → Labels d
  let μ (j : J t) (L : B j) := ∏ a, copySetProb d (L a)
  let e := splitRows (d := d) adj t ht
  let Good (Y : ∀ j, B j) := pathPoly adj s t (e.symm Y) ≠ 0
  obtain ⟨S₀,h₀⟩ := seed_graph adj s t hs hd P
  have prob := expose B μ (fun j L => Finset.prod_nonneg fun a _ => (weight_range hd (L a)).1)
    (1-delta d) (sub_nonneg.mpr (weights hd).2.2.2.2) Good (e S₀)
    (by simpa [Good] using h₀) (by
      intro Y hY j
      refine (row_step adj s t hs ht hd Y hY j).trans (le_of_eq ?_)
      apply Finset.sum_congr (by ext; simp)
      intro L _
      by_cases h : pathPoly adj s t (e.symm (Function.update Y j L)) ≠ 0 <;> simp_all only [Good,μ,ite_false,e])
  have hn : Fintype.card (NT t) = Fintype.card V - 1 := by simp [NT,Fintype.card_subtype_compl]
  rw [← hn]
  apply prob.trans (le_of_eq ?_)
  unfold copyProb
  rw [Finset.sum_filter]
  apply Finset.sum_bij' (fun Y _ => e.symm Y) (fun S _ => e S)
  · intro Y _; simp
  · intro S _; simp
  · intro Y _; exact e.apply_symm_apply Y
  · intro S _; exact e.symm_apply_apply S
  intro Y _
  by_cases h : Good Y
  · have hy : pathPoly adj s t (e.symm Y) ≠ 0 := h
    simp only [if_pos h, if_pos hy]
    let idx' := idx adj t ht
    let q := Equiv.sigmaFiberEquiv idx'
    rw [assignProb,← q.prod_comp (fun a => copySetProb d (e.symm Y a)),Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    rintro ⟨a,h⟩ _
    subst j
    rfl
  · have hy : ¬pathPoly adj s t (e.symm Y) ≠ 0 := h
    simp only [if_neg h, if_neg hy]

end DHCArcSampling

theorem solution {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
    (s t : V) (_hst : s ≠ t) (_hloop : ∀ v, ¬ adj v v) (hs : ∀ u, ¬ adj u s) (ht : ∀ v, ¬ adj t v)
    (d : ℕ) (hd : 2 ≤ d) (hham : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1 - delta d) ^ (Fintype.card V - 1) ≤
      copyProb (adj := adj) d (fun S => pathPoly adj s t S ≠ 0) := by
  obtain ⟨P,hP⟩ := hham
  exact DHCArcSampling.success adj s t hs ht d hd ⟨P,hP⟩

